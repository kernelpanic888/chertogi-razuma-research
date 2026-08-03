import CompactTentHomeomorphism

namespace BoundaryOfSelf
namespace CompactTentHomeomorphismAudit

open BiLipschitzBoundaryTransport
open CompactTentHomeomorphism

example (point : Real) : 0 <= tentBump point :=
  tentBump_nonnegative point

example (amplitude point : Real) (hAmplitude : 0 <= amplitude)
    (hSmall : amplitude < 1) (hPoint : point <= -1) :
    tentHomeomorph amplitude hAmplitude hSmall point = point := by
  rw [tentHomeomorph_apply]
  exact tentMap_identity_of_le_neg_one amplitude point hPoint

example (amplitude point : Real) (hAmplitude : 0 <= amplitude)
    (hSmall : amplitude < 1) (hPoint : 1 <= point) :
    tentHomeomorph amplitude hAmplitude hSmall point = point := by
  rw [tentHomeomorph_apply]
  exact tentMap_identity_of_one_le amplitude point hPoint

example (amplitude : Real) (hAmplitude : 0 <= amplitude)
    (hSmall : amplitude < 1) :
    StrictMono (tentMap amplitude) :=
  tentMap_strictMono amplitude hAmplitude hSmall

example (amplitude : Real) (hAmplitude : 0 <= amplitude) :
    Function.Surjective (tentMap amplitude) :=
  tentMap_surjective amplitude hAmplitude

example (amplitude : Real) (hAmplitude : 0 <= amplitude)
    (hSmall : amplitude < 1) :
    LipschitzWith (1 + amplitude).toNNReal
      (tentHomeomorph amplitude hAmplitude hSmall) :=
  (tentControlled amplitude hAmplitude hSmall).forward_lipschitz

example (amplitude : Real) (hAmplitude : 0 <= amplitude)
    (hSmall : amplitude < 1) :
    LipschitzWith (1 / (1 - amplitude)).toNNReal
      (tentHomeomorph amplitude hAmplitude hSmall).symm :=
  (tentControlled amplitude hAmplitude hSmall).inverse_lipschitz

#print axioms BoundaryOfSelf.CompactTentHomeomorphism.tentBump_lipschitz
#print axioms BoundaryOfSelf.CompactTentHomeomorphism.tentMap_strictMono
#print axioms BoundaryOfSelf.CompactTentHomeomorphism.tentMap_surjective
#print axioms BoundaryOfSelf.CompactTentHomeomorphism.tentMap_colipschitz
#print axioms BoundaryOfSelf.CompactTentHomeomorphism.tentControlled

end CompactTentHomeomorphismAudit
end BoundaryOfSelf
