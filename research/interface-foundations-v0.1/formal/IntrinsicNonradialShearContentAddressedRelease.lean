import IntrinsicNonradialShearCanonicalReplay

namespace BoundaryOfSelf.IntrinsicNonradialShearContentAddressedRelease

noncomputable section

/-! ## IF-BS-22F-F8C31F: content address and provenance are separate gates -/

/-- One path, byte count and externally computed content digest. -/
structure ArtifactDigest where
  path : String
  byteCount : Nat
  sha256 : String
  deriving Repr, DecidableEq

/-- The unsigned release statement. Cryptographic primitives remain external. -/
structure ReleaseManifest where
  schemaVersion : Nat
  releaseId : String
  signerKeyId : String
  artifacts : List ArtifactDigest
  deriving Repr, DecidableEq

/-- A verifier receives both the claimed manifest and freshly observed digests. -/
structure SignedReleaseEnvelope where
  manifest : ReleaseManifest
  observedArtifacts : List ArtifactDigest
  manifestDigest : String
  signature : String
  deriving Repr, DecidableEq

/-- Content integrity checks schema, every observed artifact and the manifest
address. It deliberately does not inspect the signature. -/
def contentAccepted
    (digestManifest : ReleaseManifest → String)
    (envelope : SignedReleaseEnvelope) : Bool :=
  envelope.manifest.schemaVersion == 1 &&
    envelope.observedArtifacts == envelope.manifest.artifacts &&
    envelope.manifestDigest == digestManifest envelope.manifest

/-- Provenance checks only possession of the key named by the manifest. It does
not inspect freshly observed artifacts. -/
def provenanceAccepted
    (verifySignature : String → String → String → Bool)
    (envelope : SignedReleaseEnvelope) : Bool :=
  verifySignature envelope.manifest.signerKeyId
    envelope.manifestDigest envelope.signature

/-- A release is accepted only when both independent gates close. -/
def releaseAccepted
    (digestManifest : ReleaseManifest → String)
    (verifySignature : String → String → String → Bool)
    (envelope : SignedReleaseEnvelope) : Bool :=
  contentAccepted digestManifest envelope &&
    provenanceAccepted verifySignature envelope

theorem contentAccepted_sound
    (digestManifest : ReleaseManifest → String)
    (envelope : SignedReleaseEnvelope)
    (haccepted : contentAccepted digestManifest envelope = true) :
    envelope.manifest.schemaVersion = 1 ∧
      envelope.observedArtifacts = envelope.manifest.artifacts ∧
      envelope.manifestDigest = digestManifest envelope.manifest := by
  simpa [contentAccepted, and_assoc] using haccepted

/-- Replacing a signature cannot change the content verdict. -/
theorem contentAccepted_signature_irrelevant
    (digestManifest : ReleaseManifest → String)
    (envelope : SignedReleaseEnvelope)
    (replacementSignature : String) :
    contentAccepted digestManifest
        { envelope with signature := replacementSignature } =
      contentAccepted digestManifest envelope :=
  rfl

/-- Replacing observed bytes cannot change the signature verdict. Therefore a
valid signature alone is not evidence that the received artifacts match. -/
theorem provenanceAccepted_observedArtifacts_irrelevant
    (verifySignature : String → String → String → Bool)
    (envelope : SignedReleaseEnvelope)
    (replacementArtifacts : List ArtifactDigest) :
    provenanceAccepted verifySignature
        { envelope with observedArtifacts := replacementArtifacts } =
      provenanceAccepted verifySignature envelope :=
  rfl

theorem releaseAccepted_eq_true_iff
    (digestManifest : ReleaseManifest → String)
    (verifySignature : String → String → String → Bool)
    (envelope : SignedReleaseEnvelope) :
    releaseAccepted digestManifest verifySignature envelope = true ↔
      contentAccepted digestManifest envelope = true ∧
      provenanceAccepted verifySignature envelope = true := by
  simp [releaseAccepted]

theorem releaseAccepted_content
    (digestManifest : ReleaseManifest → String)
    (verifySignature : String → String → String → Bool)
    (envelope : SignedReleaseEnvelope)
    (haccepted : releaseAccepted digestManifest verifySignature envelope = true) :
    contentAccepted digestManifest envelope = true :=
  (releaseAccepted_eq_true_iff digestManifest verifySignature envelope).mp
    haccepted |>.1

theorem releaseAccepted_provenance
    (digestManifest : ReleaseManifest → String)
    (verifySignature : String → String → String → Bool)
    (envelope : SignedReleaseEnvelope)
    (haccepted : releaseAccepted digestManifest verifySignature envelope = true) :
    provenanceAccepted verifySignature envelope = true :=
  (releaseAccepted_eq_true_iff digestManifest verifySignature envelope).mp
    haccepted |>.2

end

end BoundaryOfSelf.IntrinsicNonradialShearContentAddressedRelease
