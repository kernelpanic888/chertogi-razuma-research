# IF-BS-22F-F8C31H — Operational identity witness ceremony

## Core rule

`WitnessAccepted := subject matches ∧ fingerprint matches ∧ source is independent`

`AuthorRecognized := valid anchor signature ∧ WitnessAccepted`

A root fingerprint copied from the same release is not an external witness. A verifier must receive a copy from an independently controlled channel and compare it with the public key offline.

## Prepared tool

The offline ceremony tool accepts only an SPKI public key. It can:

1. derive its SHA-256 fingerprint;
2. prepare a canonical witness statement;
3. verify subject, fingerprint and independent HTTPS location from a saved witness copy;
4. reject this research site's own host as self-witnessing;
5. reject private-key input.

The tool performs no network request. This preserves the P0 public boundary and lets a reviewer save an external statement separately before verification.

## Honest boundary

The tool is ready, but the operational ceremony has not been executed. No persistent root key has been created, no custody method has been chosen, and no fingerprint has been published on an author-controlled channel. Structural acceptance of a test URL is not evidence that a real publication exists there.

## Русское чтение

Корень не может подтвердить сам себя. Локальный файл способен показать только правильный формат записи. Настоящая привязка возникает, когда тот же отпечаток независимо появляется в канале, которым управляет автор, а проверяющий приносит сохранённую копию в офлайн-проверку.
