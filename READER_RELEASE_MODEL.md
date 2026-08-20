# RR-01 / Reader Release Interface

## Canonical home and example

- Formal home: https://github.com/kernelpanic888/TMI-Lean-Formal-Library
- Reference release: https://github.com/kernelpanic888/TMI-Lean-Formal-Library/releases/tag/chertogi-first-distinction-v0.1.0
- Reference tag commit: `a5d468d1f9ffbab2beb1d213205f60f93071a5c1`

The existing release is the canonical prototype. It binds a tagged formal-home state to a self-contained public export, a source/status map, Lean artifacts, executable browser models, a live site and an explicit claim boundary.

Существующий релиз является каноническим прототипом. Он связывает состояние формального дома под тегом с самодостаточным публичным экспортом, картой источников и статусов, Lean-артефактами, исполняемыми браузерными моделями, живым сайтом и явной границей утверждений.

## Model

```text
ReaderRelease = (
  readerId,
  version,
  tag,
  commit,
  exportPath,
  publicUrl,
  sourceMap,
  formalArtifacts,
  runtimeArtifacts,
  securityBoundary,
  claimBoundary,
  englishReading,
  russianReading
)
```

```text
TMI formal home
  <-> tagged release
  <-> self-contained export
  <-> live reader
  <-> journal transition
  <-> next open seam
```

## Release body order

1. One-sentence result.
2. Live URL on the next visible line.
3. Representative image.
4. Release surface.
5. Direct reader and executable-model routes.
6. Security boundary.
7. Claim boundary.
8. Russian reading after the English reading.
9. Exact tag, commit and source-map coordinates.

## Admission

```text
tagged
and sourceMapPresent
and publicExportSelfContained
and securityBoundaryPasses
and claimBoundaryPresent
and publicUrlPresent
and returnLinkPresent
```

The release fixes a research state. It does not automatically raise the scientific status of its claims.

Релиз фиксирует состояние исследования. Он не повышает автоматически научный статус его утверждений.
