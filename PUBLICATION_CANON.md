# Publication canon · IF-0.1

Every public record inherits one route:

```text
distinction -> transition -> trace -> return
```

The route is structural, not decorative. A record must identify its own
semantic voice, source transition, inspectable trace, return path, claim
ceiling, and forbidden jumps. Shared layout does not erase the record's kind:
software speaks through transition, preprints through argument trace, reports
through recorded return, and release candidates through guarded closure.

`public/publications/records.json` is the machine-readable registry for new
release candidates. A candidate must keep `doi`, `orcidWorkId`, and
`releaseTag` null until those external publication events actually occur.

`npm run publication:check` rejects mutable formal-source links, missing claim
boundaries, and premature release identifiers.
