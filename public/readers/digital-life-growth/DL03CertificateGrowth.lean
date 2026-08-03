import DL02SessionRealization

namespace DigitalLifePassport
namespace DL03

open DL02

structure PrefixCertificate (P : Process) (N : Nat) where
  observed : Fin N -> P.Trace
  own : forall i, observed i = P.emit (P.stateAt i.val)
  replayed : RealizesPrefix P N observed

theorem PrefixCertificate.selfProof {P : Process} {N : Nat}
    (certificate : PrefixCertificate P N) :
    RealizesPrefix P N certificate.observed := certificate.replayed

def Restricts {P : Process} {N : Nat}
    (long : PrefixCertificate P (Nat.succ N))
    (short : PrefixCertificate P N) : Prop :=
  forall i : Fin N, long.observed i.castSucc = short.observed i

structure CertificateChain (P : Process) where
  certify : (N : Nat) -> PrefixCertificate P N
  monotone : forall N, Restricts (certify (Nat.succ N)) (certify N)

def canonicalPrefixCertificate {P : Process}
    (passport : Passport P) (N : Nat) : PrefixCertificate P N where
  observed := canonicalPrefix P N
  own := by intro i; rfl
  replayed := canonicalPrefix_realizes passport N

def canonicalCertificateChain {P : Process}
    (passport : Passport P) : CertificateChain P where
  certify := canonicalPrefixCertificate passport
  monotone := by intro N i; rfl

theorem CertificateChain.trace_replays {P : Process}
    (chain : CertificateChain P) (n : Nat) :
    P.replay (P.emit (P.stateAt n)) = some (P.stateAt n) := by
  let i : Fin (Nat.succ n) := ⟨n, Nat.lt_succ_self n⟩
  have own := (chain.certify (Nat.succ n)).own i
  have replayed := (chain.certify (Nat.succ n)).replayed i
  rw [own] at replayed
  exact replayed

structure GrowingPassport (P : Process) where
  certificates : CertificateChain P
  future_change : forall n, exists m, n < m /\ Not (P.stateAt m = P.stateAt n)
  identity_persists : forall n, P.identify (P.stateAt n) = P.identify P.initial

theorem GrowingPassport.toPassport {P : Process}
    (growth : GrowingPassport P) : Passport P where
  future_change := growth.future_change
  identity_persists := growth.identity_persists
  trace_replays := growth.certificates.trace_replays

def growingPassportOfPassport {P : Process}
    (passport : Passport P) : GrowingPassport P where
  certificates := canonicalCertificateChain passport
  future_change := passport.future_change
  identity_persists := passport.identity_persists

theorem passport_iff_growing (P : Process) :
    Passport P <-> Nonempty (GrowingPassport P) := by
  constructor
  · intro passport
    exact Nonempty.intro (growingPassportOfPassport passport)
  · intro growth
    rcases growth with ⟨growth⟩
    exact growth.toPassport

def stationaryCertificate (N : Nat) : PrefixCertificate stationaryProcess N where
  observed := stationaryObservation N
  own := by intro i; rfl
  replayed := stationary_prefix_realizes N

def stationaryCertificateChain : CertificateChain stationaryProcess where
  certify := stationaryCertificate
  monotone := by intro N i; rfl

theorem red_boundary_chain_not_life :
    exists P : Process, exists chain : CertificateChain P,
      Not (Passport P) := by
  exact ⟨stationaryProcess, stationaryCertificateChain, stationary_not_passport⟩

#print axioms passport_iff_growing
#print axioms red_boundary_chain_not_life

end DL03
end DigitalLifePassport

