import IntrinsicNonradialShearContentAddressedRelease

namespace BoundaryOfSelf.IntrinsicNonradialShearIdentityTrustChain

noncomputable section

/-! ## IF-BS-22F-F8C31G: external anchor and key continuity -/

structure IdentityAnchor where
  subjectName : String
  subjectId : String
  rootKeyId : String
  activeReleaseKeyId : String
  sequence : Nat
  deriving Repr, DecidableEq

structure TrustState where
  rootKeyId : String
  activeReleaseKeyId : String
  lastSequence : Nat
  revokedKeys : List String
  deriving Repr, DecidableEq

structure RotationRecord where
  sequence : Nat
  rootKeyId : String
  fromKeyId : String
  toKeyId : String
  rootApproved : Bool
  oldKeyApproved : Bool
  newKeyAccepted : Bool
  deriving Repr, DecidableEq

/-- The logical conditions checked before a rotation may advance trust. -/
structure RotationAccepted
    (state : TrustState) (rotation : RotationRecord) : Prop where
  root_matches : rotation.rootKeyId = state.rootKeyId
  from_active : rotation.fromKeyId = state.activeReleaseKeyId
  keys_differ : rotation.fromKeyId ≠ rotation.toKeyId
  next_sequence : rotation.sequence = state.lastSequence + 1
  root_approved : rotation.rootApproved = true
  old_approved : rotation.oldKeyApproved = true
  new_accepted : rotation.newKeyAccepted = true
  new_not_revoked : rotation.toKeyId ∉ state.revokedKeys

/-- Applying an accepted rotation activates the new key and permanently records
the old key as revoked. -/
def TrustState.rotate (state : TrustState) (rotation : RotationRecord) : TrustState where
  rootKeyId := state.rootKeyId
  activeReleaseKeyId := rotation.toKeyId
  lastSequence := rotation.sequence
  revokedKeys := rotation.fromKeyId :: state.revokedKeys

def TrustState.KeyTrusted (state : TrustState) (keyId : String) : Prop :=
  keyId = state.activeReleaseKeyId ∧ keyId ∉ state.revokedKeys

structure ReleaseClaim where
  sequence : Nat
  signerKeyId : String
  contentAddress : String
  signatureValid : Bool
  deriving Repr, DecidableEq

def ReleaseTrusted (state : TrustState) (release : ReleaseClaim) : Prop :=
  state.KeyTrusted release.signerKeyId ∧ release.signatureValid = true

/-- A claimed identity is recognized only when the root fingerprint arrives
from outside the release and the anchor signature is valid. -/
def IdentityAnchored
    (externallyObservedRootKeyId : String) (anchor : IdentityAnchor) : Prop :=
  externallyObservedRootKeyId = anchor.rootKeyId

def AuthorRecognized
    (externallyObservedRootKeyId : String)
    (anchorSignatureValid : Bool) (anchor : IdentityAnchor) : Prop :=
  IdentityAnchored externallyObservedRootKeyId anchor ∧
    anchorSignatureValid = true

theorem rotation_activates_new_key
    (state : TrustState) (rotation : RotationRecord) :
    (state.rotate rotation).activeReleaseKeyId = rotation.toKeyId :=
  rfl

theorem rotation_revokes_old_key
    (state : TrustState) (rotation : RotationRecord) :
    rotation.fromKeyId ∈ (state.rotate rotation).revokedKeys := by
  simp [TrustState.rotate]

theorem accepted_rotation_trusts_new_key
    (state : TrustState) (rotation : RotationRecord)
    (haccepted : RotationAccepted state rotation) :
    (state.rotate rotation).KeyTrusted rotation.toKeyId := by
  constructor
  · rfl
  · simp [TrustState.rotate, haccepted.keys_differ.symm,
      haccepted.new_not_revoked]

theorem accepted_rotation_rejects_old_key
    (state : TrustState) (rotation : RotationRecord) :
    ¬ (state.rotate rotation).KeyTrusted rotation.fromKeyId := by
  intro htrusted
  exact htrusted.2 (rotation_revokes_old_key state rotation)

theorem next_release_trusted_after_rotation
    (state : TrustState) (rotation : RotationRecord)
    (release : ReleaseClaim)
    (hrotation : RotationAccepted state rotation)
    (hsigner : release.signerKeyId = rotation.toKeyId)
    (hsignature : release.signatureValid = true) :
    ReleaseTrusted (state.rotate rotation) release := by
  constructor
  · simpa [hsigner] using accepted_rotation_trusts_new_key state rotation hrotation
  · exact hsignature

theorem old_key_release_rejected_after_rotation
    (state : TrustState) (rotation : RotationRecord)
    (release : ReleaseClaim)
    (hsigner : release.signerKeyId = rotation.fromKeyId) :
    ¬ ReleaseTrusted (state.rotate rotation) release := by
  intro htrusted
  apply accepted_rotation_rejects_old_key state rotation
  simpa [hsigner] using htrusted.1

theorem author_recognized_iff
    (externallyObservedRootKeyId : String)
    (anchorSignatureValid : Bool) (anchor : IdentityAnchor) :
    AuthorRecognized externallyObservedRootKeyId anchorSignatureValid anchor ↔
      externallyObservedRootKeyId = anchor.rootKeyId ∧
        anchorSignatureValid = true := by
  rfl

end

end BoundaryOfSelf.IntrinsicNonradialShearIdentityTrustChain
