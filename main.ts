// GitHub-compatible forge — single file, Node built-ins only (plain JS, CommonJS via require).
// Surfaces: REST /api/v3, Git smart HTTP, GraphQL and MCP.
'use strict';
const http = require('node:http');
const crypto = require('node:crypto');
const zlib = require('node:zlib');

const MAKEFUN_ENV_URL = process.env.MAKEFUN_ENV_URL || '';
const MAKEFUN_SHOP_TOKEN = process.env.MAKEFUN_SHOP_TOKEN || '';
const PORT = 0; // ephemeral

// ---------------------------------------------------------------- utilities
function sha1hex(buf) { return crypto.createHash('sha1').update(buf).digest('hex'); }
let REQ_COUNTER = 0;
function reqId() { REQ_COUNTER += 1; return 'req-' + REQ_COUNTER.toString(16).padStart(8, '0'); }
// Deterministic pseudo-time: monotonically increasing counter formatted as ISO-ish stamp.
let TIME_COUNTER = 1700000000;
function nowISO() { TIME_COUNTER += 60; return new Date(TIME_COUNTER * 1000).toISOString().replace(/\.000Z$/, 'Z'); }

function json(res, code, body, extraHeaders) {
  const payload = JSON.stringify(body);
  const headers = Object.assign({
    'Content-Type': 'application/json; charset=utf-8',
    'Content-Length': Buffer.byteLength(payload),
  }, extraHeaders || {});
  res.writeHead(code, headers);
  res.end(payload);
}

function gitObjectId(type, content) {
  return sha1hex(Buffer.concat([Buffer.from(type + ' ' + content.length + '\0'), content]));
}

function treePathSort(a, b) {
  const an = a.path, bn = b.path;
  return an < bn ? -1 : an > bn ? 1 : 0;
}

// Encode a single tree object: entries [{name, mode, type, sha}]
function encodeTree(entries) {
  entries = entries.slice().sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
  const parts = [];
  for (const e of entries) {
    parts.push(Buffer.concat([
      Buffer.from(e.mode + ' ' + e.name + '\0'),
      Buffer.from(e.sha, 'hex'),
    ]));
  }
  return Buffer.concat(parts);
}

// ---------------------------------------------------------------- store
// All state lives in memory; one process owns it. Deterministic: no wall clock persisted.
class Repo {
  constructor(owner, name) {
    this.owner = owner;
    this.name = name;
    this.id = null; // assigned by store
    this.createdAt = nowISO();
    this.updatedAt = this.createdAt;
    this.description = null;
    this.private = false;
    this.defaultBranch = 'main';
    this.issues = [];       // {number, title, body, state, labels, user, created_at, updated_at, id}
    this.pulls = [];        // like issue + head/base/ref fields
    this.labels = [];       // {id, name, color, description}
    this.objects = new Map(); // sha(hex) -> {type, data:Buffer}
    this.refs = new Map();   // ref name -> sha(hex)
    this.issueCounter = 0;
    this.pullCounter = 0;
    this.labelCounter = 0;
    this.pushCounter = 0;
  }
  refRecomputeDefault() { this.updatedAt = nowISO(); }
}

class Store {
  constructor() {
    this.repos = [];        // Repo[]
    this.userCounter = 1;
    this.repoCounter = 1000;
    this.users = new Map(); // login -> {login, id}
  }
  user(login) {
    if (!this.users.has(login)) {
      this.users.set(login, { login, id: this.userCounter++, type: 'User' });
    }
    return this.users.get(login);
  }
  findRepo(owner, name) {
    const lower = String(name).toLowerCase();
    return this.repos.find(r => r.owner === owner && r.name.toLowerCase() === lower) || null;
  }
  createRepo(owner, name, opts) {
    if (this.findRepo(owner, name)) return null;
    const repo = new Repo(owner, name);
    repo.id = this.repoCounter++;
    if (opts.description !== undefined) repo.description = opts.description ?? null;
    if (opts.private !== undefined) repo.private = !!opts.private;
    if (opts.default_branch) repo.defaultBranch = opts.default_branch;
    // Empty tree object so contents/root reads work pre-first-push.
    const treeData = encodeTree([]);
    const treeSha = gitObjectId('tree', treeData);
    repo.objects.set(treeSha, { type: 'tree', data: treeData });
    repo.emptyTree = treeSha;
    this.repos.push(repo);
    return repo;
  }
  issueNumbers(repo, pr) {
    return (pr ? repo.pulls : repo.issues);
  }
}

const store = new Store();

// ---------------------------------------------------------------- git helpers on store
function getCommitRootSha(repo) {
  const head = repo.refs.get('refs/heads/' + repo.defaultBranch);
  return head || null;
}

function parseTree(data) {
  const entries = [];
  let off = 0;
  while (off < data.length) {
    const sp = data.indexOf(0x20, off);
    const mode = data.toString('utf8', off, sp);
    const nul = data.indexOf(0x00, sp + 1);
    const name = data.toString('utf8', sp + 1, nul);
    const sha = data.toString('hex', nul + 1, nul + 21);
    entries.push({ mode, name, sha });
    off = nul + 21;
  }
  return entries;
}

// Read a path from a tree sha; returns entry or null.
function treeLookup(repo, treeSha, pathParts) {
  let cur = treeSha;
  for (let i = 0; i < pathParts.length; i++) {
    const obj = repo.objects.get(cur);
    if (!obj || obj.type !== 'tree') return null;
    const entries = parseTree(obj.data);
    const part = pathParts[i];
    const ent = entries.find(e => e.name === part);
    if (!ent) return null;
    if (i === pathParts.length - 1) return ent;
    if (ent.mode !== '040000') return null;
    cur = ent.sha;
  }
  return null;
}

function fullPathEntries(repo, commitSha) {
  // Flatten working tree of commit into map path -> {mode, sha, type}
  const out = new Map();
  const commit = repo.objects.get(commitSha);
  if (!commit || commit.type !== 'commit') return out;
  const m = /tree ([0-9a-f]{40})/.exec(commit.data.toString('utf8'));
  if (!m) return out;
  const walk = (treeSha, prefix) => {
    const obj = repo.objects.get(treeSha);
    if (!obj || obj.type !== 'tree') return;
    for (const e of parseTree(obj.data)) {
      const p = prefix ? prefix + '/' + e.name : e.name;
      if (e.mode === '040000') walk(e.sha, p);
      else out.set(p, { mode: e.mode, sha: e.sha, type: e.mode === '120000' ? 'symlink' : (e.mode === '160000' ? 'commit' : 'blob') });
    }
  };
  walk(m[1], '');
  return out;
}

function buildTreeFromPaths(repo, filesMap) {
  // filesMap: Map path -> {mode, sha}; returns root tree sha, creating needed subtrees.
  const root = new Map(); // name -> {mode, sha, subtree:Map}
  for (const [path, info] of filesMap) {
    const parts = path.split('/');
    let level = root;
    for (let i = 0; i < parts.length - 1; i++) {
      if (!level.has(parts[i])) level.set(parts[i], { mode: '040000', children: new Map() });
      level = level.get(parts[i]).children;
    }
    level.set(parts[parts.length - 1], { mode: info.mode, sha: info.sha });
  }
  const write = (map) => {
    const entries = [];
    for (const [name, v] of map) {
      if (v.children) {
        entries.push({ mode: '040000', name, sha: write(v.children) });
      } else {
        entries.push({ mode: v.mode, name, sha: v.sha });
      }
    }
    const data = encodeTree(entries);
    const sha = gitObjectId('tree', data);
    repo.objects.set(sha, { type: 'tree', data });
    return sha;
  };
  return write(root);
}

function makeCommit(repo, treeSha, parents, message, author) {
  const lines = [];
  lines.push('tree ' + treeSha);
  for (const p of parents) lines.push('parent ' + p);
  const ident = author + ' <' + author + '@users.noreply.github.example> ' + unixToGitDate(TIME_COUNTER + 60);
  lines.push('author ' + ident);
  lines.push('committer ' + ident);
  lines.push('');
  lines.push(message);
  lines.push('');
  const data = Buffer.from(lines.join('\n'));
  const sha = gitObjectId('commit', data);
  repo.objects.set(sha, { type: 'commit', data });
  return sha;
}

function unixToGitDate(unix) {
  // Deterministic git timestamp formatted like "1700000060 +0000".
  return unix + ' +0000';
}

// ---------------------------------------------------------------- REST serialization
function repoJSON(repo) {
  const owner = store.user(repo.owner);
  return {
    id: repo.id,
    node_id: 'R_' + repo.id,
    name: repo.name,
    full_name: repo.owner + '/' + repo.name,
    private: repo.private,
    owner: { login: owner.login, id: owner.id, type: owner.type },
    html_url: 'http://localhost/' + repo.owner + '/' + repo.name,
    description: repo.description,
    fork: false,
    url: 'http://localhost/api/v3/repos/' + repo.owner + '/' + repo.name,
    created_at: repo.createdAt,
    updated_at: repo.updatedAt,
    pushed_at: repo.updatedAt,
    default_branch: repo.defaultBranch,
    size: 0,
    permissions: { admin: true, maintain: true, push: true, pull: true },
  };
}

function labelJSON(repo, l) {
  return {
    id: l.id, node_id: 'L_' + l.id,
    name: l.name, color: l.color, description: l.description ?? null,
    default: false,
    url: 'http://localhost/api/v3/repos/' + repo.owner + '/' + repo.name + '/labels/' + l.name,
  };
}

function issueJSON(repo, iss, isPR) {
  const labels = iss.labels.map(n => {
    const l = repo.labels.find(x => x.name === n);
    return l ? labelJSON(repo, l) : { name: n, color: 'ededed' };
  });
  const base = {
    id: iss.id, node_id: (isPR ? 'PR_' : 'I_') + iss.id,
    number: iss.number,
    title: iss.title,
    body: iss.body ?? null,
    state: iss.state,
    locked: false,
    labels,
    user: { login: iss.user, id: 1, type: 'User' },
    created_at: iss.created_at, updated_at: iss.updated_at, closed_at: iss.closed_at ?? null,
    author_association: 'OWNER',
    url: 'http://localhost/api/v3/repos/' + repo.owner + '/' + repo.name + (isPR ? '/issues/' : '/issues/') + iss.number,
    html_url: 'http://localhost/' + repo.owner + '/' + repo.name + (isPR ? '/pull/' : '/issues/') + iss.number,
    comments: 0,
    repository_url: 'http://localhost/api/v3/repos/' + repo.owner + '/' + repo.name,
  };
  if (isPR) {
    base.pull_request = {
      url: 'http://localhost/api/v3/repos/' + repo.owner + '/' + repo.name + '/pulls/' + iss.number,
      html_url: base.html_url,
      diff_url: base.html_url + '.diff', patch_url: base.html_url + '.patch',
      merged_at: iss.merged_at ?? null,
    };
    base.merged = !!iss.merged_at;
    base.mergeable = iss.mergeable !== false;
    base.base = { ref: iss.base.ref, sha: iss.base.sha, label: iss.base.ref,
      repo: repoJSON(repo) };
    base.head = { ref: iss.head.ref, sha: iss.head.sha, label: iss.head.label || iss.head.ref,
      repo: repoJSON(repo) };
    base.merged_by = iss.merged_by ? { login: iss.merged_by, id: 1, type: 'User' } : null;
    if (iss.squash_commit) base.merge_commit_sha = iss.squash_commit;
  }
  return base;
}

// ---------------------------------------------------------------- request plumbing
function readBody(req, limit) {
  return new Promise((resolve, reject) => {
    const chunks = [];
    let total = 0;
    req.on('data', c => {
      total += c.length;
      if (limit && total > limit) { reject(new Error('payload too large')); req.destroy(); return; }
      chunks.push(c);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

function parseJSONBody(buf) {
  const text = buf.toString('utf8').trim();
  if (!text) return {};
  try { return JSON.parse(text); } catch { return undefined; }
}

// ---------------------------------------------------------------- REST routing
function requireRepo(parts, i) {
  // parts[i] = owner, parts[i+1] = repo(.git)?
  const owner = parts[i];
  const rawName = parts[i + 1] || '';
  const name = rawName.replace(/\.git$/, '');
  return store.findRepo(owner, name);
}

async function handleRest(req, res, pathname, query, body) {
  const method = req.method;
  const parts = pathname.split('/').filter(Boolean); // ['api','v3', ...]

  // /api/v3 root meta
  if (parts.length === 2) {
    return json(res, 200, {
      current_user_url: 'http://localhost/api/v3/user',
      repository_url: 'http://localhost/api/v3/repos/{owner}/{repo}',
      issue_url: 'http://localhost/api/v3/repos/{owner}/{repo}/issues/{number}',
      pull_request_url: 'http://localhost/api/v3/repos/{owner}/{repo}/pulls/{number}',
      labels_url: 'http://localhost/api/v3/repos/{owner}/{repo}/labels{/name}',
      rate_limit_url: 'http://localhost/api/v3/rate_limit',
    });
  }
  if (parts[2] === 'user' && parts.length === 3) {
    return json(res, 200, { login: 'octocat', id: 1, type: 'User', name: 'octocat', site_admin: false });
  }
  if (parts[2] === 'rate_limit') {
    return json(res, 200, { resources: { core: { limit: 5000, remaining: 5000, reset: TIME_COUNTER + 3600 } } });
  }
  if (parts[2] === 'repos') {
    if (parts.length === 3) {
      return json(res, 200, store.repos.map(repoJSON));
    }
    const repo = requireRepo(parts, 3);
    if (!repo) return json(res, 404, { message: 'Not Found', documentation_url: 'https://docs.github.com/rest' });
    const sub = parts[5];

    if (parts.length === 5) {
      if (method === 'GET') return json(res, 200, repoJSON(repo));
      if (method === 'PATCH') {
        if (body.name !== undefined) repo.name = String(body.name);
        if (body.description !== undefined) repo.description = body.description ?? null;
        if (body.private !== undefined) repo.private = !!body.private;
        if (body.default_branch !== undefined) repo.defaultBranch = String(body.default_branch);
        repo.updatedAt = nowISO();
        return json(res, 200, repoJSON(repo));
      }
      if (method === 'DELETE') {
        store.repos = store.repos.filter(r => r !== repo);
        return res.writeHead(204).end();
      }
      return json(res, 405, { message: 'Method Not Allowed' });
    }

    if (sub === 'labels') {
      if (parts.length === 6) {
        if (method === 'GET') return json(res, 200, repo.labels.map(l => labelJSON(repo, l)));
        if (method === 'POST') {
          if (!body.name) return json(res, 422, { message: 'Validation Failed' });
          if (repo.labels.some(l => l.name === body.name)) return json(res, 422, { message: 'already_exists' });
          const l = { id: ++repo.labelCounter, name: String(body.name), color: String(body.color || 'ededed').replace('#',''), description: body.description ?? null };
          repo.labels.push(l);
          return json(res, 201, labelJSON(repo, l));
        }
      } else if (parts.length === 7) {
        const name = decodeURIComponent(parts[6]);
        const idx = repo.labels.findIndex(l => l.name === name);
        if (method === 'GET') {
          if (idx < 0) return json(res, 404, { message: 'Not Found' });
          return json(res, 200, labelJSON(repo, repo.labels[idx]));
        }
        if (method === 'PATCH') {
          if (idx < 0) return json(res, 404, { message: 'Not Found' });
          const l = repo.labels[idx];
          if (body.new_name !== undefined) l.name = String(body.new_name);
          if (body.color !== undefined) l.color = String(body.color).replace('#','');
          if (body.description !== undefined) l.description = body.description ?? null;
          return json(res, 200, labelJSON(repo, l));
        }
        if (method === 'DELETE') {
          if (idx < 0) return json(res, 404, { message: 'Not Found' });
          repo.labels.splice(idx, 1);
          return res.writeHead(204).end();
        }
      }
    }

    if (sub === 'issues') {
      if (parts.length === 6) {
        if (method === 'GET') {
          let list = repo.issues.concat(repo.pulls).sort((a, b) => a.number - b.number);
          const state = query.get('state');
          if (state && state !== 'all') list = list.filter(i => i.state === state);
          if (query.get('labels')) {
            const want = query.get('labels').split(',').map(s => s.trim());
            list = list.filter(i => want.every(w => w === '' || i.labels.includes(w)));
          }
          return json(res, 200, list.map(i => issueJSON(repo, i, i.isPull)));
        }
        if (method === 'POST') {
          if (!body.title && !body.body) return json(res, 422, { message: 'Validation Failed' });
          const num = ++repo.issueCounter;
          const iss = {
            id: 10000 + num,
            number: num,
            title: String(body.title || ''),
            body: body.body ?? null,
            state: 'open',
            labels: Array.isArray(body.labels) ? body.labels.map(String) : [],
            user: 'octocat',
            created_at: nowISO(), updated_at: nowISO(),
          };
          repo.issues.push(iss);
          return json(res, 201, issueJSON(repo, iss, false));
        }
      } else if (parts.length === 7) {
        const num = parseInt(parts[6], 10);
        const iss = repo.issues.find(i => i.number === num) || repo.pulls.find(p => p.number === num);
        if (method === 'GET') {
          if (!iss) return json(res, 404, { message: 'Not Found' });
          return json(res, 200, issueJSON(repo, iss, !!iss.isPull));
        }
        if (method === 'PATCH') {
          if (!iss) return json(res, 404, { message: 'Not Found' });
          if (body.title !== undefined) iss.title = String(body.title);
          if (body.body !== undefined) iss.body = body.body ?? null;
          if (body.state !== undefined) {
            iss.state = body.state === 'closed' ? 'closed' : 'open';
            iss.closed_at = iss.state === 'closed' ? nowISO() : null;
          }
          if (Array.isArray(body.labels)) iss.labels = body.labels.map(String);
          iss.updated_at = nowISO();
          return json(res, 200, issueJSON(repo, iss, iss.isPull));
        }
      }
    }

    if (sub === 'pulls') {
      if (parts.length === 6) {
        if (method === 'GET') {
          let list = repo.pulls.slice();
          const state = query.get('state');
          if (state && state !== 'all') list = list.filter(p => p.state === state);
          return json(res, 200, list.map(p => issueJSON(repo, p, true)));
        }
        if (method === 'POST') {
          if (!body.title || !body.head || !body.base) return json(res, 422, { message: 'Validation Failed' });
          const headRef = String(body.head).replace(/^.*:/, '');
          const baseRef = String(body.base);
          const headSha = repo.refs.get('refs/heads/' + headRef);
          const baseSha = repo.refs.get('refs/heads/' + baseRef);
          if (!headSha) return json(res, 422, { message: 'head ref does not exist' });
          const pr = {
            isPull: true,
            id: 20000 + repo.pullCounter + 1,
            number: ++repo.pullCounter,
            title: String(body.title),
            body: body.body ?? null,
            state: 'open',
            labels: Array.isArray(body.labels) ? body.labels.map(String) : [],
            user: 'octocat',
            created_at: nowISO(), updated_at: nowISO(),
            head: { ref: headRef, sha: headSha, label: repo.owner + ':' + headRef },
            base: { ref: baseRef, sha: baseSha || repo.emptyTree, label: baseRef },
            merged_at: null, merged_by: null, squash_commit: null,
          };
          repo.pulls.push(pr);
          return json(res, 201, issueJSON(repo, pr, true));
        }
      } else if (parts.length === 7) {
        const num = parseInt(parts[6], 10);
        const pr = repo.pulls.find(p => p.number === num);
        if (!pr) return json(res, 404, { message: 'Not Found' });
        if (method === 'GET') return json(res, 200, issueJSON(repo, pr, true));
        if (method === 'PATCH') {
          if (body.title !== undefined) pr.title = String(body.title);
          if (body.body !== undefined) pr.body = body.body ?? null;
          if (body.state !== undefined) pr.state = body.state === 'closed' ? 'closed' : 'open';
          pr.updated_at = nowISO();
          return json(res, 200, issueJSON(repo, pr, true));
        }
      } else if (parts.length === 8 && parts[7] === 'files' && method === 'GET') {
        const num = parseInt(parts[6], 10);
        const pr = repo.pulls.find(p => p.number === num);
        if (!pr) return json(res, 404, { message: 'Not Found' });
        return json(res, 200, diffPullFiles(repo, pr));
      } else if (parts.length === 8 && parts[7] === 'merge' && method === 'PUT') {
        const num = parseInt(parts[6], 10);
        const pr = repo.pulls.find(p => p.number === num);
        if (!pr) return json(res, 404, { message: 'Not Found' });
        if (pr.merged_at) return json(res, 405, { message: 'Pull Request is not mergeable' });
        const squash = (body.merge_method || 'merge') === 'squash';
        const headSha = repo.refs.get('refs/heads/' + pr.head.ref);
        const baseSha = repo.refs.get('refs/heads/' + pr.base.ref);
        if (!headSha) return json(res, 409, { message: 'Head branch deleted' });
        // Squash merge: create one commit with base parent, tree = head tree.
        const commit = repo.objects.get(headSha);
        const m = /tree ([0-9a-f]{40})/.exec(commit.data.toString('utf8'));
        const msg = body.commit_title || ('squash: ' + pr.title);
        const newSha = makeCommit(repo, m[1], baseSha ? [baseSha] : [], msg + '\n', 'octocat');
        repo.refs.set('refs/heads/' + pr.base.ref, newSha);
        pr.merged_at = nowISO();
        pr.state = 'closed';
        pr.merged_by = 'octocat';
        pr.squash_commit = newSha;
        pr.updated_at = nowISO();
        repo.updatedAt = nowISO();
        return json(res, 200, { sha: newSha, merged: true, message: 'Pull Request successfully merged' });
      }
    }

    if (sub === 'contents') {
      if (method === 'GET') {
        const path = decodeURIComponent(parts.slice(6).join('/')) || '';
        const branch = query.get('ref') || repo.defaultBranch;
        const commitSha = repo.refs.get('refs/heads/' + branch);
        if (!commitSha) return json(res, 404, { message: 'Not Found' });
        const entries = fullPathEntries(repo, commitSha);
        if (path === '') {
          const list = [];
          for (const [p, info] of entries) {
            if (!p.includes('/')) {
              const obj = repo.objects.get(info.sha);
              list.push(contentsEntry(repo, p, info, obj ? obj.data : Buffer.alloc(0), branch));
            }
          }
          list.sort(treePathSort);
          return json(res, 200, list);
        }
        // directory?
        const dirEntries = [];
        for (const [p, info] of entries) {
          if (p.startsWith(path + '/')) {
            const rest = p.slice(path.length + 1);
            if (!rest.includes('/')) dirEntries.push(contentsEntry(repo, rest, info, repo.objects.get(info.sha)?.data || Buffer.alloc(0), branch));
          }
        }
        if (dirEntries.length) {
          dirEntries.sort(treePathSort);
          return json(res, 200, dirEntries);
        }
        const info = entries.get(path);
        if (!info) return json(res, 404, { message: 'Not Found' });
        const obj = repo.objects.get(info.sha);
        return json(res, 200, contentsEntry(repo, path, info, obj ? obj.data : Buffer.alloc(0), branch, true));
      }
      if (method === 'PUT') {
        const path = decodeURIComponent(parts.slice(6).join('/'));
        if (!path || !body.message) return json(res, 422, { message: 'Validation Failed' });
        const branch = body.branch || repo.defaultBranch;
        let commitSha = repo.refs.get('refs/heads/' + branch);
        const files = commitSha ? fullPathEntries(repo, commitSha) : new Map();
        const blobData = Buffer.from(body.content !== undefined ? (body.encoding === 'utf-8' || body.encoding === 'utf8' ? String(body.content) : Buffer.from(String(body.content).replace(/\s/g,''), 'base64')) : Buffer.alloc(0));
        const blobSha = gitObjectId('blob', blobData);
        repo.objects.set(blobSha, { type: 'blob', data: blobData });
        if (body.sha !== undefined && body.sha !== null) {
          const existing = files.get(path);
          if (!existing) return json(res, 404, { message: 'path does not exist' });
          if (existing.sha !== body.sha) {
            return json(res, 409, { message: 'is at ' + existing.sha + ' but expected ' + body.sha });
          }
          files.delete(path);
        } else {
          if (files.has(path)) {
            return json(res, 409, { message: 'path already exists' });
          }
        }
        if (body.sha !== undefined && body.sha !== null) {
          // update or delete
          if (body.content === undefined && body.delete !== true) {
            // treat as update with empty content
          }
        }
        files.set(path, { mode: '100644', sha: blobSha });
        const treeSha = buildTreeFromPaths(repo, files);
        const newCommit = makeCommit(repo, treeSha, commitSha ? [commitSha] : [], body.message + '\n', 'octocat');
        repo.refs.set('refs/heads/' + branch, newCommit);
        repo.updatedAt = nowISO();
        return json(res, 201, {
          content: contentsEntry(repo, path, { mode: '100644', sha: blobSha, type: 'blob' }, blobData, branch),
          commit: { sha: newCommit, message: body.message },
        });
      }
      if (method === 'DELETE') {
        const path = decodeURIComponent(parts.slice(6).join('/'));
        if (!path || !body.message) return json(res, 422, { message: 'Validation Failed' });
        const branch = body.branch || repo.defaultBranch;
        const commitSha = repo.refs.get('refs/heads/' + branch);
        if (!commitSha) return json(res, 404, { message: 'Not Found' });
        const files = fullPathEntries(repo, commitSha);
        const existing = files.get(path);
        if (!existing) return json(res, 404, { message: 'path does not exist' });
        if (body.sha && existing.sha !== body.sha) {
          return json(res, 409, { message: 'is at ' + existing.sha + ' but expected ' + body.sha });
        }
        files.delete(path);
        const treeSha = buildTreeFromPaths(repo, files);
        const newCommit = makeCommit(repo, treeSha, [commitSha], body.message + '\n', 'octocat');
        repo.refs.set('refs/heads/' + branch, newCommit);
        return json(res, 200, { content: null, commit: { sha: newCommit, message: body.message } });
      }
    }

    if (sub === 'git' && parts[6] === 'refs') {
      if (method === 'GET') {
        const out = [];
        for (const [name, sha] of repo.refs) {
          out.push({ ref: name, node_id: 'REF_' + name.length, url: 'http://localhost/api/v3/repos/' + repo.owner + '/' + repo.name + '/git/refs/' + name.replace('refs/', '').replace('/', '/') , object: { sha, type: 'commit' } });
        }
        return json(res, 200, out);
      }
    }
    if (sub === 'branches' && parts.length === 6) {
      if (method === 'GET') {
        const out = [];
        for (const [name, sha] of repo.refs) {
          if (!name.startsWith('refs/heads/')) continue;
          out.push({ name: name.slice('refs/heads/'.length), commit: { sha }, protected: false });
        }
        return json(res, 200, out);
      }
    }
  } else if (parts[2] === 'user' && parts[3] === 'repos' && method === 'POST') {
    if (!body.name) return json(res, 422, { message: 'Validation Failed' });
    const repo = store.createRepo('octocat', String(body.name), body);
    if (!repo) return json(res, 422, { message: 'name already exists', errors: [{ message: 'name already exists on account' }] });
    return json(res, 201, repoJSON(repo));
  } else if (parts[2] === 'orgs' && parts.length === 5 && parts[4] === 'repos' && method === 'POST') {
    if (!body.name) return json(res, 422, { message: 'Validation Failed' });
    const repo = store.createRepo(parts[3], String(body.name), body);
    if (!repo) return json(res, 422, { message: 'name already exists', errors: [{ message: 'name already exists on account' }] });
    return json(res, 201, repoJSON(repo));
  } else if (parts[2] === 'repositories' && parts.length === 3 && method === 'GET') {
    return json(res, 200, store.repos.map(repoJSON));
  }

  return json(res, 404, { message: 'Not Found', documentation_url: 'https://docs.github.com/rest' });
}

function contentsEntry(repo, path, info, data, branch, isFile) {
  const base = {
    name: path.split('/').pop(),
    path,
    sha: info.sha,
    size: data ? data.length : 0,
    url: 'http://localhost/api/v3/repos/' + repo.owner + '/' + repo.name + '/contents/' + path + '?ref=' + branch,
    html_url: 'http://localhost/' + repo.owner + '/' + repo.name + '/blob/' + branch + '/' + path,
    git_url: 'http://localhost/api/v3/repos/' + repo.owner + '/' + repo.name + '/git/blobs/' + info.sha,
    download_url: 'http://localhost/' + repo.owner + '/' + repo.name + '/raw/' + branch + '/' + path,
    type: info.type === 'tree' ? 'dir' : 'file',
    _links: { self: 'http://localhost/api/v3/repos/' + repo.owner + '/' + repo.name + '/contents/' + path + '?ref=' + branch },
  };
  if (isFile !== false && info.type !== 'tree') {
    base.encoding = 'base64';
    base.content = data.toString('base64');
  }
  return base;
}

function diffPullFiles(repo, pr) {
  const headSha = repo.refs.get('refs/heads/' + pr.head.ref) || pr.head.sha;
  const baseSha = repo.refs.get('refs/heads/' + pr.base.ref) || pr.base.sha;
  const headFiles = fullPathEntries(repo, headSha);
  const baseFiles = fullPathEntries(repo, baseSha);
  const all = new Set([...headFiles.keys(), ...baseFiles.keys()]);
  const out = [];
  let patchIdx = 0;
  for (const p of [...all].sort()) {
    const h = headFiles.get(p), b = baseFiles.get(p);
    if (h && b && h.sha === b.sha) continue;
    const status = !b ? 'added' : (!h ? 'removed' : 'modified');
    const data = h ? (repo.objects.get(h.sha)?.data || Buffer.alloc(0)) : Buffer.alloc(0);
    const prev = b ? (repo.objects.get(b.sha)?.data || Buffer.alloc(0)) : Buffer.alloc(0);
    patchIdx++;
    out.push({
      sha: h ? h.sha : b.sha,
      filename: p,
      status,
      additions: status === 'removed' ? 0 : Math.max(1, data.toString('utf8').split('\n').length),
      deletions: status === 'added' ? 0 : Math.max(1, prev.toString('utf8').split('\n').length),
      changes: 2,
      blob_url: 'http://localhost/' + repo.owner + '/' + repo.name + '/blob/' + pr.head.ref + '/' + p,
      raw_url: 'http://localhost/' + repo.owner + '/' + repo.name + '/raw/' + pr.head.ref + '/' + p,
      patch: '@@ -1 +' + (status === 'added' ? '+1' : '-1') + ' @@\n' + (status === 'removed' ? '-' : '+') + data.toString('utf8').split('\n')[0],
    });
  }
  return out;
}

// ---------------------------------------------------------------- GraphQL
// Minimal GraphQL: parse -> definitions/operations/fragments -> execute with field resolvers.
// Supports: queries, mutations, variables, operationName, fragments, aliases, nested
// selection sets, __typename, __type(name:), __schema { queryType { name } }, enums as strings.

function gqlLexer(src) {
  const tokens = [];
  let i = 0;
  const punct = '!$():=@{}[,]|&';
  while (i < src.length) {
    const c = src[i];
    if (c === '#' ) { while (i < src.length && src[i] !== '\n') i++; continue; }
    if (/\s/.test(c) || c === ',') { i++; continue; }
    if (c === '"') {
      // string (no escape-heavy handling; support \" and \\)
      let j = i + 1, out = '';
      while (j < src.length && src[j] !== '"') {
        if (src[j] === '\\' && j + 1 < src.length) { out += src[j+1] === 'n' ? '\n' : src[j+1]; j += 2; continue; }
        out += src[j]; j++;
      }
      tokens.push({ t: 'string', v: out }); i = j + 1; continue;
    }
    if (c === '.' && src[i+1] === '.' && src[i+2] === '.') { tokens.push({ t: 'spread', v: '...' }); i += 3; continue; }
    if (punct.includes(c)) { tokens.push({ t: c }); i++; continue; }
    // name (also handles numbers)
    let j = i;
    while (j < src.length && !/\s/.test(src[j]) && !punct.includes(src[j]) && src[j] !== '"' && !(src[j] === '.' && src[j+1] === '.' && src[j+2] === '.')) j++;
    if (j === i) { i++; continue; }
    tokens.push({ t: 'name', v: src.slice(i, j) });
    i = j;
  }
  return tokens;
}

function gqlParse(src) {
  const toks = gqlLexer(src);
  let pos = 0;
  const peek = () => toks[pos];
  const next = () => toks[pos++];
  const expect = t => {
    const tok = next();
    if (!tok || tok.t !== t) throw new Error('Syntax Error: expected ' + t);
    return tok;
  };
  const parseName = () => { const tok = next(); if (!tok || tok.t !== 'name') throw new Error('Syntax Error: expected name'); return tok.v; };

  function parseSelectionSet() {
    expect('{');
    const sels = [];
    while (peek() && peek().t !== '}') {
      if (peek().t === 'spread') {
        next();
        let frag = null, directives = [];
        if (peek() && peek().t === 'name' && peek().v === 'on') { next(); parseName(); /* skip type cond */ }
        if (peek() && peek().t === 'name' && peek().v !== 'on') frag = parseName();
        sels.push({ kind: 'fragment', frag });
      } else {
        let alias = null, name = parseName();
        if (peek() && peek().t === ':') { next(); alias = name; name = parseName(); }
        let args = {};
        if (peek() && peek().t === '(') {
          next();
          while (peek() && peek().t !== ')') {
            const an = parseName(); expect(':');
            args[an] = parseValueConst();
          }
          expect(')');
        }
        let sels2 = null;
        if (peek() && peek().t === '{') sels2 = parseSelectionSet();
        sels.push({ kind: 'field', name, alias, args, selections: sels2 });
      }
    }
    expect('}');
    return sels;
  }
  function skipParens() {
    let depth = 0;
    do { const t = next(); if (t.t === '(') depth++; else if (t.t === ')') depth--; } while (depth > 0 && pos < toks.length);
  }
  function parseValueConst() { return parseValue(true); }
  function parseValue(isConst) {
    const tok = next();
    if (!tok) throw new Error('Syntax Error: unexpected EOF in value');
    if (tok.t === 'string') return { kind: 'literal', value: tok.v };
    if (tok.t === 'name') {
      if (tok.v === 'true') return { kind: 'literal', value: true };
      if (tok.v === 'false') return { kind: 'literal', value: false };
      if (tok.v === 'null') return { kind: 'literal', value: null };
      if (/^-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?$/.test(tok.v)) return { kind: 'literal', value: Number(tok.v) };
      return { kind: 'literal', value: tok.v }; // enum
    }
    if (tok.t === '$') { const n = parseName(); return { kind: 'var', name: n }; }
    if (tok.t === '[') {
      const arr = [];
      while (peek() && peek().t !== ']') arr.push(parseValue(isConst));
      expect(']');
      return { kind: 'list', values: arr };
    }
    if (tok.t === '{') {
      const obj = {};
      while (peek() && peek().t !== '}') {
        const kn = parseName(); expect(':'); obj[kn] = parseValue(isConst);
      }
      expect('}');
      return { kind: 'object', value: obj };
    }
    throw new Error('Syntax Error: bad value token ' + JSON.stringify(tok));
  }

  const defs = [];
  while (pos < toks.length) {
    const tok = next();
    if (!tok) break;
    if (tok.t !== 'name' || (tok.v !== 'query' && tok.v !== 'mutation' && tok.v !== 'fragment')) {
      // anonymous shorthand query { ... }
      if (tok.t === '{') { pos--; const selections = parseSelectionSet(); defs.push({ kind: 'operation', type: 'query', name: null, selections }); continue; }
      throw new Error('Syntax Error: unexpected token');
    }
    if (tok.v === 'fragment') {
      const name = parseName();
      const onTok = next(); // 'on' is a name token
      if (!onTok || onTok.t !== 'name' || onTok.v !== 'on') throw new Error('Syntax Error: expected on');
      const typeCond = parseName();
      const selections = parseSelectionSet();
      defs.push({ kind: 'fragment', name, typeCond, selections });
      continue;
    }
    const type = tok.v;
    let name = null;
    if (peek() && peek().t === 'name') name = parseName();
    let varDefs = {};
    if (peek() && peek().t === '(') {
      next();
      while (peek() && peek().t !== ')') {
        expect('$'); const vn = parseName(); expect(':');
        // consume type tokens possibly with ! [ ]
        let depth = 0;
        while (peek()) {
          const t = peek();
          if (t.t === '[') { depth++; next(); continue; }
          if (t.t === ']') { depth--; next(); continue; }
          if (t.t === 'name' || t.t === '!') { next(); continue; }
          break;
        }
        let def = null;
        if (peek() && peek().t === '=') { next(); def = parseValueConst(); }
        varDefs[vn] = def;
      }
      expect(')');
    }
    // skip directives on operation
    while (peek() && peek().t === '@') { next(); parseName(); if (peek() && peek().t === '(') skipParens(); }
    const selections = parseSelectionSet();
    defs.push({ kind: 'operation', type, name: name || null, varDefs, selections });
  }
  return defs;
}

function resolveValue(v, variables) {
  if (!v) return null;
  if (v.kind === 'literal') return v.value;
  if (v.kind === 'var') return variables && v.name in variables ? variables[v.name] : undefined;
  if (v.kind === 'list') return v.values.map(x => resolveValue(x, variables));
  if (v.kind === 'object') { const o = {}; for (const k in v.value) o[k] = resolveValue(v.value[k], variables); return o; }
  return null;
}

// ---------------- schema description for introspection-lite
const GQL_TYPE_FIELDS = {
  Query: ['repository', 'repositoryOwner', 'viewer', 'node', 'search', 'issue', 'pullRequest', 'rateLimit'],
  Mutation: ['createPullRequest', 'mergePullRequest', 'createIssue', 'updateIssue', 'addComment', 'createRepository', 'updateRepository', 'addLabelsToLabelable'],
  Repository: ['id', 'node_id', 'name', 'nameWithOwner', 'description', 'private', 'createdAt', 'updatedAt', 'pushedAt', 'defaultBranchRef', 'isPrivate', 'isFork', 'owner', 'issue', 'issues', 'pullRequest', 'pullRequests', 'label', 'labels', 'object', 'ref', 'refs', 'stargazerCount', 'forkCount', 'url', 'databaseId', 'hasIssuesEnabled', 'primaryLanguage', 'repositoryTopics'],
  Issue: ['id', 'node_id', 'number', 'title', 'body', 'bodyText', 'bodyHTML', 'state', 'url', 'createdAt', 'updatedAt', 'closedAt', 'author', 'labels', 'comments', 'repository', 'assignees', 'stateReason'],
  PullRequest: ['id', 'node_id', 'number', 'title', 'body', 'bodyText', 'state', 'url', 'createdAt', 'updatedAt', 'closedAt', 'mergedAt', 'author', 'labels', 'comments', 'repository', 'headRefName', 'headRefOid', 'baseRefName', 'baseRefOid', 'merged', 'mergeable', 'mergedBy', 'mergeCommit', 'assignees', 'isCrossRepository', 'changedFiles', 'additions', 'deletions'],
  IssueState: null, // enum ISSUE
};

function gqlCoerceValue(typeName, raw) {
  switch (typeName) {
    case 'Int': { const n = parseInt(raw, 10); if (isNaN(n)) throw new Error('cannot coerce to Int'); return n; }
    case 'Float': { const n = parseFloat(raw); if (isNaN(n)) throw new Error('cannot coerce to Float'); return n; }
    case 'Boolean': return !!raw;
    case 'ID': case 'String': return raw === null || raw === undefined ? null : String(raw);
    default: return raw; // enums pass through as strings
  }
}

function graphqlExecute(querySrc, variables, operationName) {
  try {
    const defs = gqlParse(querySrc);
    const ops = defs.filter(d => d.kind === 'operation');
    const frags = {};
    for (const d of defs) if (d.kind === 'fragment') frags[d.name] = d;
    let op = null;
    if (operationName) op = ops.find(o => o.name === operationName);
    else if (ops.length === 1) op = ops[0];
    else if (ops.length > 1) return { errors: [{ message: 'Must provide operation name if query contains multiple operations.' }] };
    if (!op) return { errors: [{ message: 'Unknown operation named "' + operationName + '".' }] };

    const vars = {};
    for (const vn in (op.varDefs || {})) {
      if (variables && vn in variables) vars[vn] = variables[vn];
      else if (op.varDefs[vn]) vars[vn] = resolveValue(op.varDefs[vn], variables);
    }

    const ctx = { frags, vars, errors: [] };
    if (op.type === 'query') {
      const data = execSelections(op.selections, { __type: 'Query' }, null, ctx, 'Query');
      return ctx.errors.length ? { data, errors: ctx.errors } : { data };
    } else {
      const data = execSelections(op.selections, { __type: 'Mutation' }, null, ctx, 'Mutation');
      return ctx.errors.length ? { data, errors: ctx.errors } : { data };
    }
  } catch (e) {
    return { errors: [{ message: String(e.message || e) }] };
  }
}

function fieldError(ctx, msg) { ctx.errors.push({ message: msg }); }

function execSelections(selections, parent, parentRepo, ctx, typeName) {
  const out = {};
  for (const sel of selections) {
    if (sel.kind === 'fragment') {
      const frag = ctx.frags[sel.frag];
      if (frag) Object.assign(out, execSelections(frag.selections, parent, parentRepo, ctx, frag.typeCond));
      continue;
    }
    const key = sel.alias || sel.name;
    if (sel.name === '__typename') { out[key] = typeName; continue; }
    if (sel.name === '__schema') { out[key] = execSelections(sel.selections, { __schema: true }, parentRepo, ctx, '__Schema'); continue; }
    if (sel.name === '__type') {
      const tname = resolveValue(sel.args.name, ctx.vars);
      out[key] = introspectType(tname, sel.selections, ctx);
      continue;
    }
    const args = {};
    for (const an in sel.args) args[an] = resolveValue(sel.args[an], ctx.vars);
    const resolved = gqlResolveField(typeName, sel.name, args, parent, parentRepo, ctx);
    if (resolved === undefined) {
      fieldError(ctx, 'Cannot query field "' + sel.name + '" on type "' + typeName + '".');
      out[key] = null;
      continue;
    }
    if (sel.selections && resolved !== null && typeof resolved === 'object') {
      const childType = gqlFieldTypeName(typeName, sel.name, resolved);
      out[key] = execSelectionsOn(sel.selections, resolved, parentRepo, ctx, childType);
    } else if (sel.selections && resolved === null) {
      out[key] = null;
    } else {
      out[key] = resolved;
    }
  }
  return out;
}

// execSelections over a value that may be an array of homogeneous objects.
function execSelectionsOn(selections, value, parentRepo, ctx, typeName) {
  if (Array.isArray(value)) {
    return value.map(v => execSelectionsOn(selections, v, parentRepo, ctx, typeName));
  }
  return execSelections(selections, value, parentRepo, ctx, typeName);
}

function gqlFieldTypeName(parentType, fieldName, value) {
  if (value && value.__type) return value.__type;
  if (Array.isArray(value)) return gqlFieldTypeName(parentType, fieldName, value[0] || {});
  // heuristics by field name
  if (fieldName === 'issues') return 'IssueConnection';
  if (fieldName === 'pullRequests') return 'PullRequestConnection';
  if (fieldName === 'labels') return 'LabelConnection';
  if (fieldName === 'repository') return 'Repository';
  if (fieldName === 'issue') return 'Issue';
  if (fieldName === 'pullRequest') return 'PullRequest';
  if (fieldName === 'owner' || fieldName === 'author' || fieldName === 'mergedBy') return 'Actor';
  if (fieldName === 'defaultBranchRef') return 'Ref';
  if (fieldName === 'refs' || fieldName === 'ref') return 'RefConnection';
  return 'String';
}

function introspectType(name, selections, ctx) {
  if (!name) return null;
  const isEnum = name === 'IssueState' || name === 'PullRequestState' || name === 'MergeStateStatus';
  const isScalar = ['String', 'Int', 'Float', 'Boolean', 'ID', 'DateTime', 'URI', 'GitObjectID'].includes(name);
  const known = GQL_TYPE_FIELDS[name] !== undefined || isEnum || isScalar || ['Query', 'Mutation', '__Schema', '__Type', '__TypeKind', '__Field', '__InputValue', '__EnumValue', '__Directive', 'Actor', 'Ref', 'IssueConnection', 'PullRequestConnection', 'LabelConnection', 'Label', 'IssueComment', 'IssueCommentConnection', 'PageInfo', 'RepositoryConnection', 'CreatePullRequestInput', 'MergePullRequestInput', 'CreateIssueInput'].includes(name);
  if (!known) return null;
  const out = { __type: '__Type', __fake: name };
  for (const sel of flatten(selections, ctx)) {
    const key = sel.alias || sel.name;
    if (sel.name === 'name') out[key] = name;
    else if (sel.name === 'kind') out[key] = isEnum ? 'ENUM' : (isScalar ? 'SCALAR' : (['Query', 'Mutation'].includes(name) ? 'OBJECT' : 'OBJECT'));
    else if (sel.name === 'description') out[key] = '';
    else if (sel.name === 'fields') {
      const fields = (GQL_TYPE_FIELDS[name] || []).map(f => ({
        __type: '__Field',
        name: f,
        description: '',
        args: [],
        type: { __type: '__Type', kind: 'SCALAR', name: 'String', ofType: null },
      }));
      out[key] = sel.selections ? fields.map(f => execSelections(sel.selections, f, null, ctx, '__Field')) : fields;
    }
    else if (sel.name === 'enumValues') {
      const vals = name === 'IssueState' ? ['OPEN', 'CLOSED'] :
        name === 'PullRequestState' ? ['OPEN', 'CLOSED', 'MERGED'] :
        name === 'MergeStateStatus' ? ['BEHIND', 'BLOCKED', 'CLEAN', 'DIRTY', 'DRAFT', 'HAS_HOOKS', 'UNKNOWN'] :
        name === 'IssueOrderField' ? ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'] :
        [];
      const enumObjs = vals.map(v => ({ __type: '__EnumValue', name: v, description: '', isDeprecated: false, deprecationReason: null }));
      out[key] = sel.selections ? enumObjs.map(e => execSelections(sel.selections, e, null, ctx, '__EnumValue')) : enumObjs;
    }
    else if (sel.name === 'inputFields') out[key] = [];
    else if (sel.name === 'interfaces') out[key] = [];
    else if (sel.name === 'possibleTypes') out[key] = [];
    else if (sel.name === 'ofType') out[key] = null;
  }
  return out;
}

function flatten(selections, ctx) {
  const out = [];
  for (const sel of selections) {
    if (sel.kind === 'fragment' && ctx.frags[sel.frag]) out.push(...flatten(ctx.frags[sel.frag].selections, ctx));
    else out.push(sel);
  }
  return out;
}

function gqlResolveField(typeName, name, args, parent, parentRepo, ctx) {
  // top-level Query/Mutation
  if (typeName === 'Query') {
    if (name === 'viewer') return { __type: 'Actor', login: 'octocat', id: 'MDQ6VXNlcjE', resourcePath: '/octocat', url: 'http://localhost/octocat' };
    if (name === 'repository') {
      if (!args.owner || !args.name) { fieldError(ctx, 'repository requires owner and name'); return null; }
      const repo = store.findRepo(args.owner, args.name);
      if (!repo) return null;
      return repoGQL(repo);
    }
    if (name === 'repositoryOwner') {
      const u = store.user(args.login || 'octocat');
      return { __type: 'Actor', login: u.login, id: 'MDQ6VXNlcjE', url: 'http://localhost/' + u.login };
    }
    if (name === 'node') {
      const n = args.id || '';
      const m = /^(.+)\/(.+):(\d+)$/.exec(n);
      if (m) {
        const repo = store.findRepo(m[1], m[2]);
        const iss = repo && (repo.issues.find(i => 'I_' + i.id === n) || repo.pulls.find(p => 'PR_' + p.id === n));
        if (iss) return iss.isPull ? prGQL(repo, iss) : issueGQL(repo, iss);
      }
      const rm = /^R_(\d+)$/.exec(n);
      if (rm) { const repo = store.repos.find(r => 'R_' + r.id === n); if (repo) return repoGQL(repo); }
      return null;
    }
    if (name === 'rateLimit') return { __type: 'RateLimit', limit: 5000, remaining: 4999, resetAt: nowISO(), cost: 1 };
    if (name === 'search') return { __type: 'SearchResultItemConnection', issueCount: 0, nodes: [], pageInfo: { __type: 'PageInfo', hasNextPage: false, endCursor: null } };
    return undefined;
  }
  if (typeName === 'Mutation') {
    if (name === 'createPullRequest') {
      const inp = args.input || {};
      const [owner, rname] = String(inp.repositoryId || '').split('/');
      const repo = store.findRepo(owner, rname) || store.repos.find(r => 'R_' + r.id === inp.repositoryId);
      if (!repo) { fieldError(ctx, 'Could not resolve to a Repository with the id ' + inp.repositoryId); return null; }
      if (!inp.title) { fieldError(ctx, 'title is required'); return null; }
      const headRef = String(inp.headRefName || inp.baseRefName || repo.defaultBranch);
      const baseRef = String(inp.baseRefName || repo.defaultBranch);
      const headSha = repo.refs.get('refs/heads/' + headRef);
      const baseSha = repo.refs.get('refs/heads/' + baseRef);
      if (!headSha) { fieldError(ctx, 'Head ref does not exist'); return null; }
      const pr = {
        isPull: true,
        id: 20000 + repo.pullCounter + 1,
        number: ++repo.pullCounter,
        title: String(inp.title),
        body: inp.body ?? null,
        state: 'open',
        labels: [],
        user: 'octocat',
        created_at: nowISO(), updated_at: nowISO(),
        head: { ref: headRef, sha: headSha, label: repo.owner + ':' + headRef },
        base: { ref: baseRef, sha: baseSha || repo.emptyTree, label: baseRef },
        merged_at: null, merged_by: null, squash_commit: null,
      };
      repo.pulls.push(pr);
      return { __type: 'CreatePullRequestPayload', pullRequest: prGQL(repo, pr) };
    }
    if (name === 'mergePullRequest') {
      const inp = args.input || {};
      const pid = String(inp.pullRequestId || '');
      for (const repo of store.repos) {
        const pr = repo.pulls.find(p => 'PR_' + p.id === pid || 'PR_' + repo.owner + '/' + repo.name + ':' + p.number === pid);
        if (pr) {
          if (pr.merged_at) { fieldError(ctx, 'Pull Request is not mergeable'); return { __type: 'MergePullRequestPayload', pullRequest: prGQL(repo, pr), mergeCommit: null }; }
          const headSha = repo.refs.get('refs/heads/' + pr.head.ref);
          const baseSha = repo.refs.get('refs/heads/' + pr.base.ref);
          const commit = repo.objects.get(headSha);
          const m = commit && /tree ([0-9a-f]{40})/.exec(commit.data.toString('utf8'));
          const msg = inp.commitHeadline || ('squash: ' + pr.title);
          const newSha = makeCommit(repo, m ? m[1] : repo.emptyTree, baseSha ? [baseSha] : [], msg + '\n', 'octocat');
          repo.refs.set('refs/heads/' + pr.base.ref, newSha);
          pr.merged_at = nowISO(); pr.state = 'closed'; pr.merged_by = 'octocat'; pr.squash_commit = newSha; pr.updated_at = nowISO();
          return { __type: 'MergePullRequestPayload', pullRequest: prGQL(repo, pr), mergeCommit: { __type: 'Commit', oid: newSha, abbreviatedOid: newSha.slice(0, 10), message: msg, committedDate: nowISO() } };
        }
      }
      fieldError(ctx, 'Could not resolve to a PullRequest with the id ' + pid);
      return null;
    }
    if (name === 'createIssue') {
      const inp = args.input || {};
      const [owner, rname] = String(inp.repositoryId || '').split('/');
      const repo = store.findRepo(owner, rname) || store.repos.find(r => 'R_' + r.id === inp.repositoryId);
      if (!repo) { fieldError(ctx, 'Could not resolve to a Repository'); return null; }
      if (!inp.title) { fieldError(ctx, 'title is required'); return null; }
      const num = ++repo.issueCounter;
      const iss = { id: 10000 + num, number: num, title: String(inp.title), body: inp.body ?? null, state: 'open', labels: Array.isArray(inp.labelIds) ? [] : [], user: 'octocat', created_at: nowISO(), updated_at: nowISO() };
      repo.issues.push(iss);
      return { __type: 'CreateIssuePayload', issue: issueGQL(repo, iss) };
    }
    if (name === 'updateIssue') {
      const inp = args.input || {};
      for (const repo of store.repos) {
        const iss = repo.issues.find(i => 'I_' + i.id === String(inp.id || '')) || repo.pulls.find(p => 'PR_' + p.id === String(inp.id || ''));
        if (iss) {
          if (inp.title !== undefined) iss.title = String(inp.title);
          if (inp.body !== undefined) iss.body = inp.body ?? null;
          if (inp.state !== undefined) { iss.state = inp.state === 'CLOSED' ? 'closed' : 'open'; iss.closed_at = iss.state === 'closed' ? nowISO() : null; }
          iss.updated_at = nowISO();
          return { __type: 'UpdateIssuePayload', issue: iss.isPull ? prGQL(repo, iss) : issueGQL(repo, iss) };
        }
      }
      fieldError(ctx, 'Could not resolve to an Issue');
      return null;
    }
    if (name === 'createRepository' || name === 'updateRepository') {
      const inp = args.input || {};
      if (name === 'createRepository') {
        if (!inp.name) { fieldError(ctx, 'name is required'); return null; }
        const owner = inp.ownerId ? String(inp.ownerId).replace(/^U_/, 'octocat') : 'octocat';
        const repo = store.createRepo(owner === 'octocat' && inp.ownerId && !inp.ownerId.startsWith('octocat') ? inp.ownerId : owner, String(inp.name), { description: inp.description, private: inp.visibility === 'PRIVATE' });
        if (!repo) { fieldError(ctx, 'name already exists'); return null; }
        return { __type: 'CreateRepositoryPayload', repository: repoGQL(repo) };
      }
      return { __type: 'UpdateRepositoryPayload', repository: null };
    }
    if (name === 'addComment') {
      const inp = args.input || {};
      for (const repo of store.repos) {
        const iss = repo.issues.find(i => 'I_' + i.id === String(inp.subjectId || ''));
        if (iss) {
          iss.updated_at = nowISO();
          return { __type: 'AddCommentPayload', issue: issueGQL(repo, iss) };
        }
      }
      fieldError(ctx, 'Could not resolve subject');
      return null;
    }
    if (name === 'addLabelsToLabelable') return { __type: 'AddLabelsToLabelablePayload' };
    return undefined;
  }

  // object fields
  const p = parent || {};
  switch (typeName) {
    case '__Schema':
      if (name === 'queryType') return { __type: '__Type', name: 'Query', kind: 'OBJECT' };
      if (name === 'mutationType') return { __type: '__Type', name: 'Mutation', kind: 'OBJECT' };
      if (name === 'types') return ['Query', 'Mutation', 'Repository', 'Issue', 'PullRequest', 'IssueState', 'String', 'Int', 'Boolean', 'ID', 'DateTime'].map(n => ({ __type: '__Type', name: n, kind: 'SCALAR' }));
      if (name === 'directives') return [];
      return null;
    case '__Type': case '__Field': case '__EnumValue':
      return p[name] !== undefined ? p[name] : null;
    case 'Actor':
      if (name === 'login') return p.login || 'octocat';
      if (name === 'id') return p.id || 'MDQ6VXNlcjE';
      if (name === 'url') return p.url || 'http://localhost/octocat';
      if (name === 'avatarUrl') return 'http://localhost/avatars/u/1';
      if (name === '__typename') return 'User';
      return undefined;
    case 'Repository': {
      const repo = p.__repo;
      if (!repo) return null;
      if (name === 'id' || name === 'node_id') return 'R_' + repo.id;
      if (name === 'databaseId') return repo.id;
      if (name === 'name') return repo.name;
      if (name === 'nameWithOwner') return repo.owner + '/' + repo.name;
      if (name === 'description') return repo.description;
      if (name === 'isPrivate' || name === 'private') return repo.private;
      if (name === 'createdAt') return repo.createdAt;
      if (name === 'updatedAt') return repo.updatedAt;
      if (name === 'pushedAt') return repo.updatedAt;
      if (name === 'url') return 'http://localhost/' + repo.owner + '/' + repo.name;
      if (name === 'owner') return { __type: 'Actor', login: repo.owner };
      if (name === 'defaultBranchRef') return repo.refs.get('refs/heads/' + repo.defaultBranch) ? { __type: 'Ref', name: repo.defaultBranch, prefix: 'refs/heads/', target: { __type: 'Commit', oid: repo.refs.get('refs/heads/' + repo.defaultBranch) } } : null;
      if (name === 'hasIssuesEnabled') return true;
      if (name === 'isFork') return false;
      if (name === 'stargazerCount' || name === 'forkCount') return 0;
      if (name === 'primaryLanguage') return null;
      if (name === 'repositoryTopics') return { __type: 'RepositoryTopicConnection', nodes: [] };
      if (name === 'issue' || name === 'pullRequest') {
        const n = args.number;
        const list = name === 'issue' ? repo.issues : repo.pulls;
        const iss = list.find(i => i.number === n);
        if (!iss) return null;
        return iss.isPull ? prGQL(repo, iss) : issueGQL(repo, iss);
      }
      if (name === 'issues' || name === 'pullRequests') {
        let list = (name === 'issues' ? repo.issues.concat(repo.pulls) : repo.pulls).slice();
        if (args.states && Array.isArray(args.states)) list = list.filter(i => args.states.includes(i.state.toUpperCase()));
        else if (args.states) list = list.filter(i => args.states === i.state.toUpperCase());
        if (name === 'issues' && args.states && !Array.isArray(args.states) && args.states === 'OPEN') { /* keep */ }
        if (args.orderBy && args.orderBy.field === 'UPDATED_AT') list.sort((a, b) => a.updated_at < b.updated_at ? 1 : -1);
        const first = args.first || 20;
        const map = new Map();
        for (const i of list.slice(0, first)) map.set(i.isPull ? prGQL(repo, i) : issueGQL(repo, i), i.isPull ? 'PullRequest' : 'Issue');
        const nodes = [...map.keys()].map(n2 => n2);
        return { __type: name === 'issues' ? 'IssueConnection' : 'PullRequestConnection', nodes, edges: nodes.map(n2 => ({ __type: 'IssueEdge', node: n2, cursor: 'cursor' })), totalCount: list.length, pageInfo: { __type: 'PageInfo', hasNextPage: list.length > first, endCursor: 'cursor', startCursor: 'cursor' } };
      }
      if (name === 'label' || name === 'labels') {
        if (name === 'label') { const l = repo.labels.find(l => l.name === args.name); return l ? { __type: 'Label', name: l.name, color: l.color, id: 'L_' + l.id, description: l.description } : null; }
        return { __type: 'LabelConnection', nodes: repo.labels.map(l => ({ __type: 'Label', name: l.name, color: l.color, id: 'L_' + l.id, description: l.description })), totalCount: repo.labels.length, pageInfo: { hasNextPage: false } };
      }
      if (name === 'object') {
        const sha = args.oid || getCommitRootSha(repo);
        if (sha && args.expression === 'HEAD') { const h = getCommitRootSha(repo); return h ? { __type: 'Commit', oid: h } : null; }
        return sha && repo.objects.get(sha) ? { __type: 'Commit', oid: sha, __repo: repo } : null;
      }
      if (name === 'ref' || name === 'refs') {
        if (name === 'ref') {
          let qualified = args.qualifiedName || '';
          if (!qualified && args.name) qualified = 'refs/heads/' + args.name;
          const sha = repo.refs.get(qualified);
          return sha ? { __type: 'Ref', name: qualified.replace(/^refs\/heads\//, ''), prefix: 'refs/heads/', target: { __type: 'Commit', oid: sha } } : null;
        }
        const nodes = [];
        for (const [rn, sha] of repo.refs) {
          if (rn.startsWith('refs/heads/')) nodes.push({ __type: 'Ref', name: rn.slice(11), prefix: 'refs/heads/', target: { __type: 'Commit', oid: sha } });
        }
        return { __type: 'RefConnection', nodes, totalCount: nodes.length, pageInfo: { hasNextPage: false } };
      }
      return undefined;
    }
    case 'Issue': case 'PullRequest': {
      const repo = parentRepo || p.__repo;
      const iss = p.__iss;
      if (!iss) return null;
      if (name === 'id' || name === 'node_id') return (typeName === 'PullRequest' ? 'PR_' : 'I_') + iss.id;
      if (name === 'databaseId') return iss.id;
      if (name === 'number') return iss.number;
      if (name === 'title') return iss.title;
      if (name === 'body' || name === 'bodyText' || name === 'bodyHTML') return iss.body === null ? null : (name === 'bodyHTML' ? '<p>' + String(iss.body).replace(/&/g,'&amp;').replace(/</g,'&lt;') + '</p>' : iss.body);
      if (name === 'state') return iss.state === 'open' ? 'OPEN' : (iss.merged_at ? 'MERGED' : 'CLOSED');
      if (name === 'stateReason') return iss.state === 'closed' ? 'COMPLETED' : null;
      if (name === 'url') return 'http://localhost/' + (repo ? repo.owner + '/' + repo.name : '') + (typeName === 'PullRequest' ? '/pull/' : '/issues/') + iss.number;
      if (name === 'createdAt') return iss.created_at;
      if (name === 'updatedAt') return iss.updated_at;
      if (name === 'closedAt') return iss.closed_at || null;
      if (name === 'author') return { __type: 'Actor', login: iss.user };
      if (name === 'repository') return repo ? repoGQL(repo) : null;
      if (name === 'labels') return { __type: 'LabelConnection', nodes: iss.labels.map(n2 => { const l = repo.labels.find(x => x.name === n2); return { __type: 'Label', name: n2, color: l ? l.color : 'ededed', id: 'L_' + (l ? l.id : 0) }; }), totalCount: iss.labels.length, pageInfo: { hasNextPage: false } };
      if (name === 'comments') return { __type: 'IssueCommentConnection', nodes: [], totalCount: 0, pageInfo: { hasNextPage: false } };
      if (name === 'assignees') return { nodes: [], totalCount: 0, pageInfo: { hasNextPage: false } };
      if (typeName === 'PullRequest') {
        if (name === 'mergedAt') return iss.merged_at || null;
        if (name === 'merged') return !!iss.merged_at;
        if (name === 'mergeable') return 'MERGEABLE';
        if (name === 'mergedBy') return iss.merged_by ? { __type: 'Actor', login: iss.merged_by } : null;
        if (name === 'headRefName') return iss.head.ref;
        if (name === 'headRefOid') return iss.head.sha;
        if (name === 'baseRefName') return iss.base.ref;
        if (name === 'baseRefOid') return iss.base.sha;
        if (name === 'mergeCommit') return iss.squash_commit ? { __type: 'Commit', oid: iss.squash_commit, abbreviatedOid: iss.squash_commit.slice(0, 10) } : null;
        if (name === 'isCrossRepository') return false;
        if (name === 'changedFiles') return 1;
        if (name === 'additions' || name === 'deletions') return 0;
      }
      return undefined;
    }
    case 'CreatePullRequestPayload':
      if (name === 'pullRequest') return p.pullRequest;
      return undefined;
    case 'MergePullRequestPayload':
      if (name === 'pullRequest') return p.pullRequest;
      if (name === 'mergeCommit') return p.mergeCommit;
      return undefined;
    case 'CreateIssuePayload':
      if (name === 'issue') return p.issue;
      return undefined;
    case 'UpdateIssuePayload':
      if (name === 'issue') return p.issue;
      return undefined;
    case 'CreateRepositoryPayload':
      if (name === 'repository') return p.repository;
      return undefined;
    case 'AddCommentPayload':
      if (name === 'issue') return p.issue;
      return undefined;
    case 'IssueConnection': case 'PullRequestConnection': case 'LabelConnection': case 'RefConnection': case 'IssueCommentConnection': case 'RepositoryTopicConnection': case 'SearchResultItemConnection': case 'RepositoryConnection':
      if (name === 'nodes') return p.nodes || [];
      if (name === 'edges') return p.edges || [];
      if (name === 'totalCount') return p.totalCount || 0;
      if (name === 'issueCount') return p.totalCount || 0;
      if (name === 'pageInfo') return p.pageInfo || { hasNextPage: false };
      return undefined;
    case 'IssueEdge':
      if (name === 'node') return p.node;
      if (name === 'cursor') return p.cursor;
      return undefined;
    case 'PageInfo':
      if (name === 'hasNextPage') return !!p.hasNextPage;
      if (name === 'endCursor') return p.endCursor || null;
      if (name === 'startCursor') return p.startCursor || null;
      if (name === 'hasPreviousPage') return false;
      return undefined;
    case 'Ref':
      if (name === 'name') return p.name;
      if (name === 'prefix') return p.prefix;
      if (name === 'target') return p.target;
      if (name === 'id') return 'ref:' + p.name;
      return undefined;
    case 'Commit':
      if (name === 'oid') return p.oid;
      if (name === 'abbreviatedOid') return (p.oid || '').slice(0, 10);
      if (name === 'message') return p.message || '';
      if (name === 'committedDate') return p.committedDate || nowISO();
      if (name === 'history') return { nodes: [], pageInfo: { hasNextPage: false } };
      return undefined;
    case 'Label':
      if (name === 'name') return p.name;
      if (name === 'color') return p.color;
      if (name === 'id') return p.id;
      if (name === 'description') return p.description || null;
      return undefined;
    case 'Actor': break;
    case 'RateLimit':
      if (name === 'limit') return p.limit;
      if (name === 'remaining') return p.remaining;
      if (name === 'resetAt') return p.resetAt;
      if (name === 'cost') return p.cost;
      return undefined;
    case 'IssueComment':
      return undefined;
  }
  return undefined;
}

function repoGQL(repo) {
  return { __type: 'Repository', __repo: repo };
}
function issueGQL(repo, iss) {
  return { __type: 'Issue', __repo: repo, __iss: iss };
}
function prGQL(repo, pr) {
  return { __type: 'PullRequest', __repo: repo, __iss: pr };
}

// ---------------------------------------------------------------- MCP
const MCP_TOOLS = [
  {
    name: 'create_repo',
    description: 'Create a new repository',
    inputSchema: { type: 'object', properties: { name: { type: 'string', description: 'Repository name' }, description: { type: 'string' }, private: { type: 'boolean' }, owner: { type: 'string' } }, required: ['name'] },
  },
  {
    name: 'get_repo',
    description: 'Get repository details',
    inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' } }, required: ['owner', 'repo'] },
  },
  {
    name: 'create_issue',
    description: 'Create an issue',
    inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, title: { type: 'string' }, body: { type: 'string' }, labels: { type: 'array', items: { type: 'string' } } }, required: ['owner', 'repo', 'title'] },
  },
  {
    name: 'list_issues',
    description: 'List issues',
    inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, state: { type: 'string', enum: ['open', 'closed', 'all'] } }, required: ['owner', 'repo'] },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request',
    inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, title: { type: 'string' }, head: { type: 'string' }, base: { type: 'string' }, body: { type: 'string' } }, required: ['owner', 'repo', 'title', 'head', 'base'] },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request (squash by default)',
    inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, number: { type: 'number' }, merge_method: { type: 'string', enum: ['merge', 'squash', 'rebase'] } }, required: ['owner', 'repo', 'number'] },
  },
  {
    name: 'list_repos',
    description: 'List repositories',
    inputSchema: { type: 'object', properties: {} },
  },
];

function mcpToolResult(name, args) {
  switch (name) {
    case 'create_repo': {
      const owner = args.owner || 'octocat';
      const repo = store.createRepo(owner, String(args.name), { description: args.description, private: args.private });
      if (!repo) return { content: [{ type: 'text', text: 'repository already exists' }], isError: true };
      return { content: [{ type: 'text', text: JSON.stringify(repoJSON(repo), null, 2) }] };
    }
    case 'get_repo': {
      const repo = store.findRepo(args.owner, args.repo);
      if (!repo) return { content: [{ type: 'text', text: 'repository not found' }], isError: true };
      return { content: [{ type: 'text', text: JSON.stringify(repoJSON(repo), null, 2) }] };
    }
    case 'create_issue': {
      const repo = store.findRepo(args.owner, args.repo);
      if (!repo) return { content: [{ type: 'text', text: 'repository not found' }], isError: true };
      const num = ++repo.issueCounter;
      const iss = { id: 10000 + num, number: num, title: String(args.title), body: args.body ?? null, state: 'open', labels: Array.isArray(args.labels) ? args.labels.map(String) : [], user: 'octocat', created_at: nowISO(), updated_at: nowISO() };
      repo.issues.push(iss);
      return { content: [{ type: 'text', text: JSON.stringify(issueJSON(repo, iss, false), null, 2) }] };
    }
    case 'list_issues': {
      const repo = store.findRepo(args.owner, args.repo);
      if (!repo) return { content: [{ type: 'text', text: 'repository not found' }], isError: true };
      let list = repo.issues.concat(repo.pulls);
      if (args.state && args.state !== 'all') list = list.filter(i => i.state === args.state);
      list.sort((a, b) => a.number - b.number);
      return { content: [{ type: 'text', text: JSON.stringify(list.map(i => ({ number: i.number, title: i.title, state: i.state, pull_request: !!i.isPull })), null, 2) }] };
    }
    case 'create_pull_request': {
      const repo = store.findRepo(args.owner, args.repo);
      if (!repo) return { content: [{ type: 'text', text: 'repository not found' }], isError: true };
      const headRef = String(args.head).replace(/^.*:/, '');
      const baseRef = String(args.base);
      const headSha = repo.refs.get('refs/heads/' + headRef);
      if (!headSha) return { content: [{ type: 'text', text: 'head ref does not exist' }], isError: true };
      const pr = {
        isPull: true, id: 20000 + repo.pullCounter + 1, number: ++repo.pullCounter,
        title: String(args.title), body: args.body ?? null, state: 'open', labels: [], user: 'octocat',
        created_at: nowISO(), updated_at: nowISO(),
        head: { ref: headRef, sha: headSha, label: repo.owner + ':' + headRef },
        base: { ref: baseRef, sha: repo.refs.get('refs/heads/' + baseRef) || repo.emptyTree, label: baseRef },
        merged_at: null, merged_by: null, squash_commit: null,
      };
      repo.pulls.push(pr);
      return { content: [{ type: 'text', text: JSON.stringify(issueJSON(repo, pr, true), null, 2) }] };
    }
    case 'merge_pull_request': {
      const repo = store.findRepo(args.owner, args.repo);
      if (!repo) return { content: [{ type: 'text', text: 'repository not found' }], isError: true };
      const pr = repo.pulls.find(p => p.number === args.number);
      if (!pr) return { content: [{ type: 'text', text: 'pull request not found' }], isError: true };
      if (pr.merged_at) return { content: [{ type: 'text', text: 'pull request already merged' }], isError: true };
      const headSha = repo.refs.get('refs/heads/' + pr.head.ref);
      const baseSha = repo.refs.get('refs/heads/' + pr.base.ref);
      const commit = repo.objects.get(headSha);
      const m = commit && /tree ([0-9a-f]{40})/.exec(commit.data.toString('utf8'));
      const newSha = makeCommit(repo, m ? m[1] : repo.emptyTree, baseSha ? [baseSha] : [], (args.commit_title || ('squash: ' + pr.title)) + '\n', 'octocat');
      repo.refs.set('refs/heads/' + pr.base.ref, newSha);
      pr.merged_at = nowISO(); pr.state = 'closed'; pr.merged_by = 'octocat'; pr.squash_commit = newSha; pr.updated_at = nowISO();
      return { content: [{ type: 'text', text: JSON.stringify({ sha: newSha, merged: true }, null, 2) }] };
    }
    case 'list_repos':
      return { content: [{ type: 'text', text: JSON.stringify(store.repos.map(r => r.owner + '/' + r.name), null, 2) }] };
    default:
      return { content: [{ type: 'text', text: 'unknown tool: ' + name }], isError: true };
  }
}

function mcpHandle(body) {
  // single message or batch; streamable HTTP transport (no sessions required)
  const respond = msg => msg;
  if (Array.isArray(body)) {
    return body.map(mcpHandleOne);
  }
  return mcpHandleOne(body);
}

function mcpHandleOne(msg) {
  if (!msg || typeof msg !== 'object' || msg.jsonrpc !== '2.0') {
    return { jsonrpc: '2.0', error: { code: -32600, message: 'Invalid Request' }, id: null };
  }
  const id = msg.id !== undefined ? msg.id : null;
  if (msg.method === 'initialize') {
    return {
      jsonrpc: '2.0', id,
      result: {
        protocolVersion: '2024-11-05',
        capabilities: { tools: { listChanged: false } },
        serverInfo: { name: 'forge-mcp', version: '1.0.0' },
        instructions: 'GitHub-compatible forge MCP server',
      },
    };
  }
  if (msg.method === 'notifications/initialized' || msg.method === 'initialized') {
    return null; // notification: no response
  }
  if (msg.method === 'ping') return { jsonrpc: '2.0', id, result: {} };
  if (msg.method === 'tools/list') {
    return { jsonrpc: '2.0', id, result: { tools: MCP_TOOLS } };
  }
  if (msg.method === 'tools/call') {
    const p = msg.params || {};
    const r = mcpToolResult(p.name, p.arguments || {});
    return { jsonrpc: '2.0', id, result: r };
  }
  if (msg.method === 'resources/list') return { jsonrpc: '2.0', id, result: { resources: [] } };
  if (msg.method === 'prompts/list') return { jsonrpc: '2.0', id, result: { prompts: [] } };
  return { jsonrpc: '2.0', error: { code: -32601, message: 'Method not found' }, id };
}

// Local-only Git smart HTTP support for the single-file Forge. No child processes or git executable.
const GIT_ZERO = '0000000000000000000000000000000000000000';
const GIT_FLUSH = Buffer.from('0000');
const GIT_DELIM = Buffer.from('0001');
const GIT_AGENT = 'forge/1.0';

function gitPkt(value) {
  const b = Buffer.isBuffer(value) ? value : Buffer.from(String(value), 'utf8');
  const n = b.length + 4;
  if (n > 65520) throw new Error('pkt-line too large');
  return Buffer.concat([Buffer.from(n.toString(16).padStart(4, '0'), 'ascii'), b]);
}
function gitPktText(s) { return gitPkt(Buffer.from(s, 'utf8')); }
function gitReadPackets(buf, start = 0) {
  const packets = [];
  let p = start;
  while (p + 4 <= buf.length) {
    const head = buf.toString('ascii', p, p + 4);
    if (!/^[0-9a-fA-F]{4}$/.test(head)) break;
    const len = parseInt(head, 16);
    if (len === 0) { packets.push({ type: 'flush', data: Buffer.alloc(0) }); p += 4; break; }
    if (len === 1) { packets.push({ type: 'delim', data: Buffer.alloc(0) }); p += 4; continue; }
    if (len === 2) { packets.push({ type: 'response-end', data: Buffer.alloc(0) }); p += 4; continue; }
    if (len < 4 || p + len > buf.length) throw new Error('invalid pkt-line length');
    packets.push({ type: 'data', data: buf.subarray(p + 4, p + len) });
    p += len;
  }
  return { packets, next: p, tail: buf.subarray(p) };
}
function gitBytesEq(a, b) { return a.length === b.length && a.equals(b); }
function gitSend(res, code, contentType, body) {
  res.writeHead(code, {
    'Content-Type': contentType,
    'Content-Length': body.length,
    'Cache-Control': 'no-cache, max-age=0, must-revalidate',
    Pragma: 'no-cache',
  });
  res.end(body);
}
function gitRefAdvertisement(repo, service) {
  const caps = service === 'git-receive-pack'
    ? `report-status delete-refs ofs-delta agent=${GIT_AGENT} object-format=sha1 symref=HEAD:refs/heads/${repo.defaultBranch}`
    : `multi_ack_detailed side-band-64k thin-pack ofs-delta shallow deepen-since deepen-not no-progress include-tag multi_ack agent=${GIT_AGENT} object-format=sha1 symref=HEAD:refs/heads/${repo.defaultBranch}`;
  const out = [gitPktText(`# service=${service}\n`), GIT_FLUSH];
  const refs = [...repo.refs.entries()].filter(([name, sha]) => name.startsWith('refs/') && /^[0-9a-f]{40}$/.test(sha)).sort((a, b) => a[0].localeCompare(b[0]));
  if (!refs.length) {
    out.push(gitPktText(`${GIT_ZERO} capabilities^{}\0${caps}\n`));
  } else {
    const head = repo.refs.get(`refs/heads/${repo.defaultBranch}`) || refs[0][1];
    out.push(gitPktText(`${head} HEAD\0${caps}\n`));
    for (const [name, sha] of refs) out.push(gitPktText(`${sha} ${name}\n`));
  }
  out.push(GIT_FLUSH);
  return Buffer.concat(out);
}
function gitV2Advertisement() {
  return Buffer.concat([
    gitPktText('version 2\n'),
    gitPktText(`agent=${GIT_AGENT}\n`),
    gitPktText('ls-refs=unborn\n'),
    gitPktText('fetch=shallow wait-for-done\n'),
    gitPktText('object-format=sha1\n'),
    GIT_FLUSH,
  ]);
}
function gitLsRefs(repo, args) {
  const symrefs = args.includes('symrefs');
  const unborn = args.includes('unborn');
  const prefixes = args.filter(x => x.startsWith('ref-prefix ')).map(x => x.slice(11));
  const include = name => !prefixes.length || prefixes.some(p => name.startsWith(p));
  const out = [];
  const refs = [...repo.refs.entries()].filter(([name, sha]) => name.startsWith('refs/') && /^[0-9a-f]{40}$/.test(sha)).sort((a, b) => a[0].localeCompare(b[0]));
  const headRef = `refs/heads/${repo.defaultBranch}`;
  const headSha = repo.refs.get(headRef);
  if (headSha && include('HEAD')) out.push(gitPktText(`${headSha} HEAD${symrefs ? ` symref-target:${headRef}` : ''}\n`));
  else if (!headSha && unborn && include('HEAD')) out.push(gitPktText(`unborn HEAD symref-target:${headRef}\n`));
  for (const [name, sha] of refs) if (include(name)) out.push(gitPktText(`${sha} ${name}\n`));
  out.push(GIT_FLUSH);
  return Buffer.concat(out);
}
function gitVisitObjects(repo, wants, depth) {
  const objects = [], seen = new Set(), shallow = new Set();
  function visit(sha, commitDepth) {
    if (seen.has(sha)) return;
    const obj = repo.objects.get(sha);
    if (!obj) throw new Error('object not found: ' + sha);
    seen.add(sha);
    objects.push({ sha, type: obj.type, data: obj.data });
    if (obj.type === 'commit') {
      const text = obj.data.toString('utf8');
      const tree = /^tree ([0-9a-f]{40})/m.exec(text);
      if (tree) visit(tree[1], commitDepth);
      const parents = [...text.matchAll(/^parent ([0-9a-f]{40})/gm)].map(m => m[1]);
      if (depth > 0 && commitDepth >= depth && parents.length) shallow.add(sha);
      else for (const p of parents) visit(p, commitDepth + 1);
    } else if (obj.type === 'tree') {
      for (const e of parseTree(obj.data)) {
        if (e.mode !== '160000' && repo.objects.has(e.sha)) visit(e.sha, commitDepth);
      }
    } else if (obj.type === 'tag') {
      const target = /^object ([0-9a-f]{40})/m.exec(obj.data.toString('utf8'));
      if (target) visit(target[1], commitDepth);
    }
  }
  for (const w of wants) visit(w, 1);
  return { objects, shallow: [...shallow].sort() };
}
function gitPackHeader(type, size) {
  const types = { commit: 1, tree: 2, blob: 3, tag: 4 };
  const t = types[type];
  if (!t) throw new Error('unsupported object type ' + type);
  let n = size, first = (t << 4) | (n & 15); n = Math.floor(n / 16);
  const out = [];
  if (n) first |= 0x80;
  out.push(first);
  while (n) { let b = n & 0x7f; n = Math.floor(n / 128); if (n) b |= 0x80; out.push(b); }
  return Buffer.from(out);
}
function gitMakePack(objects) {
  const parts = [Buffer.from('PACK'), Buffer.from([0, 0, 0, 2]), Buffer.alloc(4)];
  parts[2].writeUInt32BE(objects.length, 0);
  for (const o of objects) parts.push(gitPackHeader(o.type, o.data.length), zlib.deflateSync(o.data));
  const body = Buffer.concat(parts);
  return Buffer.concat([body, crypto.createHash('sha1').update(body).digest()]);
}
function gitReadVarint(buf, state) {
  let n = 0, shift = 0, b;
  do { if (state.p >= buf.length) throw new Error('truncated delta varint'); b = buf[state.p++]; n += (b & 0x7f) * Math.pow(2, shift); shift += 7; } while (b & 0x80);
  return n;
}
function gitApplyDelta(base, delta) {
  const st = { p: 0 };
  const baseSize = gitReadVarint(delta, st), resultSize = gitReadVarint(delta, st);
  if (baseSize !== base.length) throw new Error('delta base size mismatch');
  const chunks = []; let total = 0;
  while (st.p < delta.length) {
    const cmd = delta[st.p++];
    if (cmd & 0x80) {
      let off = 0, size = 0;
      if (cmd & 0x01) off |= delta[st.p++];
      if (cmd & 0x02) off |= delta[st.p++] << 8;
      if (cmd & 0x04) off |= delta[st.p++] << 16;
      if (cmd & 0x08) off += delta[st.p++] * 0x1000000;
      if (cmd & 0x10) size |= delta[st.p++];
      if (cmd & 0x20) size |= delta[st.p++] << 8;
      if (cmd & 0x40) size |= delta[st.p++] << 16;
      if (!size) size = 0x10000;
      if (off + size > base.length) throw new Error('delta copy out of bounds');
      const chunk = base.subarray(off, off + size); chunks.push(chunk); total += chunk.length;
    } else if (cmd) {
      if (st.p + cmd > delta.length) throw new Error('truncated delta insert');
      const chunk = delta.subarray(st.p, st.p + cmd); st.p += cmd; chunks.push(chunk); total += chunk.length;
    } else throw new Error('invalid delta opcode');
  }
  if (total !== resultSize) throw new Error('delta result size mismatch');
  return Buffer.concat(chunks, total);
}
function gitParsePack(repo, pack) {
  if (pack.length < 32 || pack.toString('ascii', 0, 4) !== 'PACK') throw new Error('invalid PACK signature');
  const version = pack.readUInt32BE(4), count = pack.readUInt32BE(8), end = pack.length - 20;
  if (version !== 2 && version !== 3) throw new Error('unsupported PACK version');
  const digest = crypto.createHash('sha1').update(pack.subarray(0, end)).digest();
  if (!digest.equals(pack.subarray(end))) throw new Error('PACK checksum mismatch');
  let p = 12; const entries = [], byOffset = new Map(), bySha = new Map();
  for (let ix = 0; ix < count; ix++) {
    const start = p;
    if (p >= end) throw new Error('truncated PACK entry');
    let b = pack[p++], type = (b >> 4) & 7, size = b & 15, shift = 4;
    while (b & 0x80) { if (p >= end) throw new Error('truncated PACK size'); b = pack[p++]; size += (b & 0x7f) * Math.pow(2, shift); shift += 7; }
    let baseOffset = null, baseSha = null;
    if (type === 6) {
      if (p >= end) throw new Error('truncated ofs-delta');
      b = pack[p++]; let dist = b & 0x7f;
      while (b & 0x80) { if (p >= end) throw new Error('truncated ofs-delta offset'); b = pack[p++]; dist = (dist + 1) * 128 + (b & 0x7f); }
      baseOffset = start - dist;
    } else if (type === 7) {
      if (p + 20 > end) throw new Error('truncated ref-delta');
      baseSha = pack.toString('hex', p, p + 20); p += 20;
    }
    const z = zlib.inflateSync(pack.subarray(p, end), { info: true });
    const used = z.engine.bytesWritten;
    if (!used || p + used > end) throw new Error('bad compressed object');
    p += used;
    const raw = z.buffer;
    if (raw.length !== size) throw new Error('PACK object size mismatch');
    const types = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };
    if (types[type]) {
      const o = { type: types[type], data: raw, sha: gitObjectId(types[type], raw), offset: start, delta: false };
      entries.push(o); byOffset.set(start, o); bySha.set(o.sha, o);
    } else if (type === 6 || type === 7) {
      const o = { type: null, data: null, deltaData: raw, baseOffset, baseSha, sha: null, offset: start, delta: true };
      entries.push(o); byOffset.set(start, o);
    } else throw new Error('invalid PACK object type ' + type);
  }
  if (p !== end) throw new Error('PACK trailing bytes');
  let pending = entries.filter(o => o.delta), rounds = 0;
  while (pending.length && rounds++ <= entries.length) {
    const next = [];
    for (const o of pending) {
      const base = o.baseOffset !== null ? byOffset.get(o.baseOffset) : (bySha.get(o.baseSha) || repo.objects.get(o.baseSha));
      if (!base || !base.type || !base.data) { next.push(o); continue; }
      o.data = gitApplyDelta(base.data, o.deltaData); o.type = base.type; o.sha = gitObjectId(o.type, o.data); o.delta = false;
      bySha.set(o.sha, o);
    }
    pending = next;
  }
  if (pending.length) throw new Error('unresolved PACK delta base');
  for (const o of entries) repo.objects.set(o.sha, { type: o.type, data: o.data });
  return entries.map(o => o.sha);
}
function gitPktLinesToText(parsed) {
  return parsed.packets.filter(p => p.type === 'data').map(p => p.data.toString('utf8').replace(/\n$/, ''));
}
function gitHandleUploadV2(repo, body, res) {
  const parsed = gitReadPackets(body), lines = gitPktLinesToText(parsed);
  const cmd = (lines.find(x => x.startsWith('command=')) || '').slice(8);
  const delim = parsed.packets.findIndex(p => p.type === 'delim');
  const args = delim < 0 ? [] : parsed.packets.slice(delim + 1).filter(p => p.type === 'data').map(p => p.data.toString('utf8').replace(/\n$/, ''));
  if (cmd === 'ls-refs') return gitSend(res, 200, 'application/x-git-upload-pack-result', gitLsRefs(repo, args));
  if (cmd !== 'fetch') return gitSend(res, 400, 'application/x-git-upload-pack-result', Buffer.from('unsupported command'));
  const wants = args.filter(x => x.startsWith('want ')).map(x => x.slice(5).trim());
  if (!wants.length) return gitSend(res, 400, 'application/x-git-upload-pack-result', Buffer.from('missing want'));
  const d = args.find(x => x.startsWith('deepen ')); const depth = d ? Math.max(0, parseInt(d.slice(7), 10) || 0) : 0;
  const selected = gitVisitObjects(repo, wants, depth);
  const pack = gitMakePack(selected.objects);
  const out = [];
  if (depth > 0) {
    out.push(gitPktText('shallow-info\n'));
    for (const sha of selected.shallow) out.push(gitPktText(`shallow ${sha}\n`));
    out.push(GIT_DELIM);
  }
  out.push(gitPktText('packfile\n'));
  for (let i = 0; i < pack.length; i += 65000) out.push(gitPkt(Buffer.concat([Buffer.from([1]), pack.subarray(i, i + 65000)])));
  out.push(GIT_FLUSH);
  return gitSend(res, 200, 'application/x-git-upload-pack-result', Buffer.concat(out));
}
function gitHandleUploadV0(repo, body, res) {
  const parsed = gitReadPackets(body), lines = gitPktLinesToText(parsed);
  const wants = [], args = [];
  let side = false;
  for (const line0 of lines) {
    const line = line0.split('\0')[0];
    if (line.startsWith('want ')) {
      const fields = line0.split('\0'); wants.push(line.slice(5).split(' ')[0]);
      if (fields[1] && /side-band-64k|side-band/.test(fields[1])) side = true;
    } else if (line.startsWith('deepen ')) args.push(line);
  }
  if (!wants.length) return gitSend(res, 400, 'application/x-git-upload-pack-result', Buffer.from('missing want'));
  const depthLine = args.find(x => x.startsWith('deepen '));
  const depth = depthLine ? Math.max(0, parseInt(depthLine.slice(7), 10) || 0) : 0;
  const selected = gitVisitObjects(repo, wants, depth), pack = gitMakePack(selected.objects);
  const out = [gitPktText('NAK\n')];
  if (side) {
    for (let i = 0; i < pack.length; i += 64000) out.push(gitPkt(Buffer.concat([Buffer.from([1]), pack.subarray(i, i + 64000)])));
    out.push(GIT_FLUSH);
  } else out.push(pack);
  return gitSend(res, 200, 'application/x-git-upload-pack-result', Buffer.concat(out));
}
function gitHandleReceivePack(repo, body, res) {
  const parsed = gitReadPackets(body), updates = [];
  for (const p of parsed.packets) {
    if (p.type === 'flush') break;
    if (p.type !== 'data') continue;
    const line = p.data.toString('utf8').replace(/\n$/, '').split('\0')[0];
    const m = /^([0-9a-f]{40}) ([0-9a-f]{40}) (\S+)$/.exec(line);
    if (m) updates.push({ old: m[1], next: m[2], ref: m[3] });
  }
  if (!updates.length) return gitSend(res, 200, 'application/x-git-receive-pack-result', Buffer.alloc(0));
  let unpackError = null;
  if (parsed.tail.length) {
    try { gitParsePack(repo, parsed.tail); } catch (e) { unpackError = String(e.message || e); }
  } else if (updates.some(u => u.next !== GIT_ZERO && !repo.objects.has(u.next))) {
    unpackError = 'missing packfile';
  }
  const statuses = [];
  for (const u of updates) {
    const current = repo.refs.get(u.ref) || GIT_ZERO;
    if (unpackError) statuses.push(`ng ${u.ref} ${unpackError}\n`);
    else if (current !== u.old) statuses.push(`ng ${u.ref} stale info\n`);
    else if (u.next !== GIT_ZERO && !repo.objects.has(u.next)) statuses.push(`ng ${u.ref} object not found\n`);
    else if (u.next === GIT_ZERO) { repo.refs.delete(u.ref); statuses.push(`ok ${u.ref}\n`); }
    else {
      repo.refs.set(u.ref, u.next);
      if (u.ref.startsWith('refs/heads/') && repo.refs.size === 1) repo.defaultBranch = u.ref.slice('refs/heads/'.length);
      repo.refRecomputeDefault();
      repo.pushCounter++;
      statuses.push(`ok ${u.ref}\n`);
    }
  }
  const out = [gitPktText(`unpack ${unpackError ? 'error ' + unpackError : 'ok'}\n`), ...statuses.map(gitPktText), GIT_FLUSH];
  return gitSend(res, 200, 'application/x-git-receive-pack-result', Buffer.concat(out));
}
async function gitSmartHttp(req, res, pathname, searchParams) {
  const m = /^\/([^/]+)\/([^/]+?)(?:\.git)?(?:\/(info\/refs|git-upload-pack|git-receive-pack))\/?$/.exec(pathname);
  if (!m) return json(res, 404, { message: 'Repository not found' });
  const owner = decodeURIComponent(m[1]), name = decodeURIComponent(m[2]), endpoint = m[3] || '';
  const repo = store.findRepo(owner, name);
  if (!repo) return json(res, 404, { message: 'Repository not found' });
  if (endpoint === 'info/refs') {
    const service = searchParams.get('service');
    if (service !== 'git-upload-pack' && service !== 'git-receive-pack') return json(res, 403, { message: 'Unsupported Git service' });
    const v2 = service === 'git-upload-pack' && /(?:^|:)version=2(?:$|:)/.test(req.headers['git-protocol'] || '');
    const body = v2 ? gitV2Advertisement() : gitRefAdvertisement(repo, service);
    return gitSend(res, 200, `application/x-${service}-advertisement`, body);
  }
  if (endpoint === 'git-upload-pack' && req.method === 'POST') {
    const body = await readBody(req, 64 * 1024 * 1024);
    const v2 = /(?:^|:)version=2(?:$|:)/.test(req.headers['git-protocol'] || '');
    return v2 ? gitHandleUploadV2(repo, body, res) : gitHandleUploadV0(repo, body, res);
  }
  if (endpoint === 'git-receive-pack' && req.method === 'POST') {
    const body = await readBody(req, 128 * 1024 * 1024);
    return gitHandleReceivePack(repo, body, res);
  }
  return res.writeHead(405, { Allow: endpoint === 'info/refs' ? 'GET' : 'POST' }).end();
}

const server = http.createServer(async (req, res) => {
  const id = reqId();
  res.setHeader('X-GitHub-Request-Id', id);
  res.setHeader('X-GitHub-Media-Type', 'github.v3; format=json');
  const u = new URL(req.url, 'http://localhost');
  const pathname = u.pathname;

  // Auth: harness bearer token required on all routes.
  if (MAKEFUN_SHOP_TOKEN) {
    const auth = req.headers.authorization || '';
    if (auth !== 'Bearer ' + MAKEFUN_SHOP_TOKEN && auth !== 'token ' + MAKEFUN_SHOP_TOKEN) {
      return json(res, 401, { message: 'Requires authentication', documentation_url: 'https://docs.github.com/rest' });
    }
  }

  try {
    if (pathname.startsWith('/api/v3')) {
      const buf = await readBody(req, 64 * 1024 * 1024);
      const body = (methodHasBody(req.method) ? parseJSONBody(buf) : (buf.length ? parseJSONBody(buf) : {}));
      if (body === undefined) return json(res, 400, { message: 'Problems parsing JSON' });
      return await handleRest(req, res, pathname, u.searchParams, body);
    }
    if (pathname === '/api/graphql' || pathname === '/graphql') {
      const buf = await readBody(req, 8 * 1024 * 1024);
      const body = parseJSONBody(buf);
      if (body === undefined) return json(res, 400, { message: 'Problems parsing JSON' });
      if (req.method !== 'POST' && req.method !== 'GET') return json(res, 405, { message: 'Method Not Allowed' });
      const result = graphqlExecute(body.query || '', body.variables || {}, body.operationName || null);
      return json(res, 200, result);
    }
    if (pathname === '/mcp') {
      const buf = await readBody(req, 8 * 1024 * 1024);
      if (req.method !== 'POST' && req.method !== 'GET') return json(res, 405, { message: 'Method Not Allowed' });
      if (req.method === 'GET') return res.writeHead(405, { allow: 'POST' }).end();
      const body = parseJSONBody(buf);
      if (body === undefined) return json(res, 400, { jsonrpc: '2.0', error: { code: -32700, message: 'Parse error' }, id: null });
      const out = mcpHandle(body);
      if (out === null || (Array.isArray(out) && out.length === 0)) return res.writeHead(202).end();
      return json(res, 200, out);
    }
    if (/^\/[^/]+\/[^/]+(?:\.git)?\/(?:info\/refs|git-upload-pack|git-receive-pack)$/.test(pathname)) {
      return await gitSmartHttp(req, res, pathname, u.searchParams);
    }
    return json(res, 404, { message: 'Not Found' });
  } catch (err) {
    return json(res, 500, { message: 'Internal Server Error' });
  }
});

function methodHasBody(m) { return m === 'POST' || m === 'PUT' || m === 'PATCH' || m === 'DELETE'; }

// ---------------------------------------------------------------- harness lifecycle
async function registerAndPoll(port) {
  if (!MAKEFUN_ENV_URL) {
    console.error('MAKEFUN_ENV_URL not set; running without harness registration');
    return;
  }
  const reg = await fetch(MAKEFUN_ENV_URL + '/register', {
    method: 'POST',
    headers: { 'content-type': 'application/json', authorization: 'Bearer ' + MAKEFUN_SHOP_TOKEN },
    body: JSON.stringify({ port }),
  });
  if (!reg.ok) console.error('register failed:', reg.status);
  const poll = setInterval(async () => {
    try {
      const r = await fetch(MAKEFUN_ENV_URL + '/done');
      if (r.ok) {
        const j = await r.json();
        if (j && j.done) { clearInterval(poll); server.close(); process.exit(0); }
      }
    } catch { /* retry */ }
  }, 1000);
}

server.listen(PORT, '127.0.0.1', () => {
  const addr = server.address();
  console.log('forge listening on 127.0.0.1:' + addr.port);
  registerAndPoll(addr.port).catch(e => console.error('harness error:', e.message));
});
