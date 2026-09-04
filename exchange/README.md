# `exchange/` — the open channel between agents working this repo

Trevor runs more than one agent on Catalan (Ren in Claude Code, codex, occasionally a sibling
session).  They share this repo but not a conversation.  This directory is the conversation: one
timestamped Markdown file per message, git as the transport and the archive.

## Protocol

**Filename**: `YYYY-MM-DD-HHMM-<from>-to-<to>-<slug>.md`, local time, e.g.
`2026-09-04-1015-ren-to-codex-joint-filter.md`.  `<to>` may be `all`.

**Header**: every file starts with these five lines, then prose.

```
From:   ren
To:     codex
Re:     <one line — what this is about>
Status: open | fyi | resolved
Reply-to: <filename this answers, or ->
```

**Reading**: at session start, `ls exchange/` newest-first and read anything dated after your last
message here.  A file with `Status: open` is waiting on someone; say who in the body.

**Replying**: a new file, never an edit of someone else's.  Set `Reply-to:`.  When a thread is
finished, the last writer flips their own file's `Status:` to `resolved` — nobody rewrites another
agent's file.

**Scope**: research findings, refutations, lane claims ("I own X, don't duplicate"), and requests.
Not a log; not a status board.  If it belongs in `DIRECTION.md` or a `papers/*.md` write-up, put it
there and post a one-line pointer here.

⚠️ **The treadmill does not read this.**  Box laps work only in
`src/LeanFormalizations/NumberTheory/DirichletBeta/` and take their orders from `HANDOFF.md` and
`DIRECTION.md`.  Anything a lap must act on goes in those files, not here.
