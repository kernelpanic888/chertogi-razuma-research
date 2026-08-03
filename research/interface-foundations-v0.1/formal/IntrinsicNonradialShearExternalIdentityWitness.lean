import IntrinsicNonradialShearIdentityTrustChain

namespace BoundaryOfSelf.IntrinsicNonradialShearExternalIdentityWitness

noncomputable section

open IntrinsicNonradialShearIdentityTrustChain

/-! ## IF-BS-22F-F8C31H: an identity root cannot witness itself -/

structure ExternalIdentityWitness where
  subjectName : String
  subjectId : String
  rootKeyId : String
  observedRootKeyId : String
  publicationUri : String
  sourceIndependent : Bool
  deriving Repr, DecidableEq

/-- Acceptance requires the same subject, the same root fingerprint, a matching
observation and an independently supplied source. -/
structure WitnessAccepted
    (anchor : IdentityAnchor) (witness : ExternalIdentityWitness) : Prop where
  subject_name_matches : witness.subjectName = anchor.subjectName
  subject_id_matches : witness.subjectId = anchor.subjectId
  root_matches : witness.rootKeyId = anchor.rootKeyId
  observation_matches : witness.observedRootKeyId = witness.rootKeyId
  source_independent : witness.sourceIndependent = true

def AuthorRecognizedByWitness
    (anchorSignatureValid : Bool)
    (anchor : IdentityAnchor) (witness : ExternalIdentityWitness) : Prop :=
  anchorSignatureValid = true ∧ WitnessAccepted anchor witness

theorem accepted_witness_has_matching_root
    (anchor : IdentityAnchor) (witness : ExternalIdentityWitness)
    (haccepted : WitnessAccepted anchor witness) :
    witness.observedRootKeyId = anchor.rootKeyId := by
  calc
    witness.observedRootKeyId = witness.rootKeyId :=
      haccepted.observation_matches
    _ = anchor.rootKeyId := haccepted.root_matches

theorem self_witness_rejected
    (anchor : IdentityAnchor) (witness : ExternalIdentityWitness)
    (hself : witness.sourceIndependent = false) :
    ¬ WitnessAccepted anchor witness := by
  intro haccepted
  have hindependent := haccepted.source_independent
  rw [hself] at hindependent
  exact Bool.noConfusion hindependent

theorem wrong_observation_rejected
    (anchor : IdentityAnchor) (witness : ExternalIdentityWitness)
    (hmismatch : witness.observedRootKeyId ≠ anchor.rootKeyId) :
    ¬ WitnessAccepted anchor witness := by
  intro haccepted
  exact hmismatch (accepted_witness_has_matching_root anchor witness haccepted)

theorem recognized_author_requires_external_witness
    (anchorSignatureValid : Bool)
    (anchor : IdentityAnchor) (witness : ExternalIdentityWitness)
    (hrecognized :
      AuthorRecognizedByWitness anchorSignatureValid anchor witness) :
    WitnessAccepted anchor witness :=
  hrecognized.2

theorem recognized_author_requires_valid_anchor_signature
    (anchorSignatureValid : Bool)
    (anchor : IdentityAnchor) (witness : ExternalIdentityWitness)
    (hrecognized :
      AuthorRecognizedByWitness anchorSignatureValid anchor witness) :
    anchorSignatureValid = true :=
  hrecognized.1

end

end BoundaryOfSelf.IntrinsicNonradialShearExternalIdentityWitness
