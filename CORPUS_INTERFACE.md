# CI-01 / Corpus Interface

## Интерфейс целостного корпуса

The corpus is not a pile of pages. It is a directed interface graph connecting an idea, its public reading, its canonical source, its journal transition and its formal or executable model.

Корпус является не набором страниц, а направленным графом интерфейсов, связывающим идею, публичное чтение, канонический исходник, журнальный переход и формальную либо исполняемую модель.

For every public research object:

```text
idea <-> reader <-> Git source <-> journal <-> formal/runtime model
```

Git is the source of truth. The site is the public projection. A missing transition is recorded as `OPEN SEAM`; it is never replaced by an invented reference.

Git является источником истины. Сайт является публичной проекцией. Отсутствующий переход получает статус `OPEN SEAM` и никогда не заменяется выдуманной ссылкой.

## Canonical artifacts

- [Machine-readable interface registry](public/corpus/interfaces.json)
- [Self-contained public corpus reader](public/readers/corpus-interface/index.html)
- [Bilingual field journal](journal/README.md)
- [Live corpus interface](https://chertogi-razuma-research.kernelpanic888.chatgpt.site/readers/corpus-interface/)

## Invariant

```text
sourceOf(publicReader) = canonicalGitPath
publicProjection(canonicalGitPath) = publicReader
```

A deployment is admitted only after the source tree builds, the public security boundary passes and the interface registry has no dangling local path.

Публикация допускается только после сборки исходного дерева, проверки публичной границы безопасности и отсутствия оборванных локальных путей в реестре интерфейсов.
