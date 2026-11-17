# GitHub-compatible forge

A single-process Git forge written in `main.ts` for Node.js 22, using only Node built-ins. It provides a GitHub-style REST v3 surface, GraphQL, MCP over HTTP, and Git smart HTTP (`receive-pack` v0 and `upload-pack` v2). Repository, issue, pull request, and Git object state lives in the process's in-memory store.

## Run

Start with Node 22:

```sh
MAKEFUN_SHOP_TOKEN=<local-token> node main.ts
```

The server binds an ephemeral loopback port and prints its address. When the harness supplies `MAKEFUN_ENV_URL` and `MAKEFUN_SHOP_TOKEN`, the process registers the port with the harness and observes its completion endpoint. All HTTP routes require the configured bearer token when `MAKEFUN_SHOP_TOKEN` is set.

## Interfaces

- REST API: `/api/v3`
- GraphQL: `/api/graphql`
- MCP (Streamable HTTP): `/mcp`
- Git smart HTTP repositories: `/<owner>/<repo>.git` (clone/fetch and push)

There are no runtime package dependencies, external services, or shell-outs to Git.

## License

MIT. See [`LICENSE`](LICENSE).
