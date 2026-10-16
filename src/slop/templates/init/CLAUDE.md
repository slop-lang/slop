@AGENTS.md

## Claude Code

The `slop` MCP server is registered in `.mcp.json`. Claude Code asks you once
to approve it. Its tools show up as `mcp__slop__ref`, `mcp__slop__doc`,
`mcp__slop__check` and `mcp__slop__format`.

These project skills live in `.claude/skills/`:

- `slop-style`: how to write idiomatic SLOP, contract first.
- `slop-pitfalls`: mistakes agents often make in SLOP. Load it before
  writing or fixing SLOP.
- `slop-review`: a checklist for reviewing SLOP code.

Run `slop init --agents-only` after you upgrade slop. It refreshes these
skills, and adds the `slop` server to any MCP config that lacks it. It does
not touch `AGENTS.md` or this file, which are yours to edit.
