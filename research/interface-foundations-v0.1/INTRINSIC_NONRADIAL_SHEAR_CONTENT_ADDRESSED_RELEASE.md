# IF-BS-22F-F8C31F — Content-addressed release and provenance

## Claim

A release is accepted only when two independent checks pass:

`C(B,M) := ∧ᵢ H(Bᵢ)=hᵢ ∧ H(M)=m`

`P(M,σ,K) := Verify_K(H(M),σ)`

`Accept := C ∧ P`

Content integrity `C` says that the received bytes match the addressed manifest. Provenance `P` says that the signature matches the public key named by that manifest. Neither statement implies the other.

## Verified slice

- The Lean carrier proves that changing a signature cannot change the content verdict.
- It separately proves that changing observed artifacts cannot change the signature verdict.
- The release verifier hashes every listed artifact with SHA-256, replays the F8C31E rational fixture, hashes the canonical manifest, derives the public-key identifier and verifies an Ed25519 signature.
- A changed artifact is rejected while the unchanged signature remains valid.
- A changed signature is rejected while the unchanged content remains valid.

## Honest boundary

Lean proves the logical composition around abstract digest and signature functions; it does not implement or prove SHA-256 or Ed25519. The current public key is carried by the release itself. Therefore the signature proves possession of its matching private key, not the civil identity of the author. Identity requires an independently published key fingerprint or another trusted external anchor.

## Русское чтение

Проверка содержимого отвечает на вопрос «те ли это байты?». Подпись отвечает на другой вопрос: «владел ли подписавший закрытым ключом, соответствующим указанному открытому ключу?». Математическая истинность не следует ни из хеша, ни из подписи. Поэтому выпуск принимается только как совместное прохождение двух независимых ворот, а привязка ключа к личности остаётся отдельной красной границей.
