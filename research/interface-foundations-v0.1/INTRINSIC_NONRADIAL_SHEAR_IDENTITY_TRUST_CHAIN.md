# IF-BS-22F-F8C31G — Identity anchor and key continuity

## Separation

The content gate remains unchanged. Identity is a different statement:

`ContentAccepted := C`

`RotationAccepted := Sig_root ∧ Sig_old ∧ Sig_new`

`AuthorRecognized := ChainContinuous ∧ ExternalWitness(root fingerprint)`

An embedded root key cannot witness itself. The verifier therefore accepts a trusted root fingerprint only as an explicit external input.

## Two-release chain

1. The identity root signs an anchor naming release key A.
2. Release 1 is signed by key A and addresses the F8C31F manifest.
3. A rotation record is signed by the identity root, key A and key B.
4. The record activates B and revokes A beginning with release sequence 2.
5. Release 2 is signed by B, links to release 1 and the rotation record, and addresses a canonical five-artifact F8C31G content manifest.

The negative fixture is deliberately signed by the real old private key A after the rotation. Its Ed25519 signature is valid, but policy rejects it because A is revoked. This distinguishes cryptographic validity from current authorization.

## Honest boundary

The fixture proves protocol mechanics and key continuity. Its content gate independently checks the formal carrier, audit, verifier, reader and passport listed by release 2. The private fixture keys existed only in memory and were discarded. The root fingerprint has not been independently published on ORCID, GitHub or another author-controlled channel, so the public page must continue to show identity binding as open.

## Русское чтение

Подпись старым ключом может оставаться математически корректной после отзыва, но перестаёт быть допустимой. Ротация принимается только при трёх согласиях: корневого, старого и нового ключей. Имя автора признаётся лишь тогда, когда отпечаток корневого ключа приходит из независимого канала, а не из самого проверяемого выпуска.
