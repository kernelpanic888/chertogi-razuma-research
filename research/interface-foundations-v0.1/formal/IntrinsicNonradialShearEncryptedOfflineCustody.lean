import IntrinsicNonradialShearExternalIdentityWitness

namespace BoundaryOfSelf.IntrinsicNonradialShearEncryptedOfflineCustody

noncomputable section

/-! ## IF-BS-22F-F8C31I: encrypted offline custody preflight -/

structure CustodyProfile where
  outsideRelease : Bool
  privateKeyEncrypted : Bool
  directoryMode : Nat
  privateKeyMode : Nat
  passphraseStoredTogether : Bool
  overwriteAllowed : Bool
  recoveryVerified : Bool
  deriving Repr, DecidableEq

/-- Decimal 448 and 384 are POSIX modes 0700 and 0600. -/
structure CustodyAccepted (profile : CustodyProfile) : Prop where
  outside_release : profile.outsideRelease = true
  encrypted : profile.privateKeyEncrypted = true
  directory_private : profile.directoryMode = 448
  key_private : profile.privateKeyMode = 384
  passphrase_separate : profile.passphraseStoredTogether = false
  no_overwrite : profile.overwriteAllowed = false
  recovery_verified : profile.recoveryVerified = true

def CeremonyReady
    (publicWitnessToolReady : Bool) (profile : CustodyProfile) : Prop :=
  publicWitnessToolReady = true ∧ CustodyAccepted profile

theorem accepted_custody_is_outside_release
    (profile : CustodyProfile) (haccepted : CustodyAccepted profile) :
    profile.outsideRelease = true :=
  haccepted.outside_release

theorem accepted_custody_is_encrypted
    (profile : CustodyProfile) (haccepted : CustodyAccepted profile) :
    profile.privateKeyEncrypted = true :=
  haccepted.encrypted

theorem workspace_custody_rejected
    (profile : CustodyProfile) (hinside : profile.outsideRelease = false) :
    ¬ CustodyAccepted profile := by
  intro haccepted
  have houtside := haccepted.outside_release
  rw [hinside] at houtside
  exact Bool.noConfusion houtside

theorem plaintext_custody_rejected
    (profile : CustodyProfile)
    (hplaintext : profile.privateKeyEncrypted = false) :
    ¬ CustodyAccepted profile := by
  intro haccepted
  have hencrypted := haccepted.encrypted
  rw [hplaintext] at hencrypted
  exact Bool.noConfusion hencrypted

theorem colocated_passphrase_rejected
    (profile : CustodyProfile)
    (hcolocated : profile.passphraseStoredTogether = true) :
    ¬ CustodyAccepted profile := by
  intro haccepted
  have hseparate := haccepted.passphrase_separate
  rw [hcolocated] at hseparate
  exact Bool.noConfusion hseparate

theorem ready_ceremony_has_safe_custody
    (publicWitnessToolReady : Bool) (profile : CustodyProfile)
    (hready : CeremonyReady publicWitnessToolReady profile) :
    CustodyAccepted profile :=
  hready.2

end

end BoundaryOfSelf.IntrinsicNonradialShearEncryptedOfflineCustody
