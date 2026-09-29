import ForestUnimodality.Stage350JointInputs
import ForestUnimodality.Stage350JointDirectionData.Case33
import ForestUnimodality.Stage350JointTailData.Case33Part00
import ForestUnimodality.Stage350JointTailData.Case33Part01
import ForestUnimodality.Stage350JointTailData.Case33Part02
import ForestUnimodality.Stage350JointTailData.Case33Part03
import ForestUnimodality.Stage350JointTailData.Case33Part04
import ForestUnimodality.Stage350JointTailData.Case33Part05
import ForestUnimodality.Stage350JointTailData.Case33Part06
import ForestUnimodality.Stage350JointTailData.Case33Part07

namespace ForestUnimodality.Stage350JointInputsData.Case33
open Real Set JointDirectionBudget ReciprocalGradientBudget Stage350JointInputs
open Stage350JointDirectionData.Case33
open Stage350JointTailData.Case33
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def theta : ℝ := (8183031/12500000)
noncomputable def ratioMax : ℝ := (40/53)
def reverse : Bool := false
noncomputable def profiles : ℕ→GradientProfile
  | 0 => .thirtyOne
  | 1 => .thirtyOne
  | 2 => .thirtyOne
  | 3 => .thirtyOne
  | 4 => .thirtyOne
  | 5 => .thirtyOne
  | 6 => .thirtyOne
  | 7 => .thirtyOne
  | 8 => .thirtyOne
  | 9 => .thirtyOne
  | 10 => .thirtyOne
  | 11 => .thirtyOne
  | 12 => .thirtyOne
  | 13 => .thirtyOne
  | 14 => .thirtyOne
  | 15 => .thirtyOne
  | 16 => .thirtyOne
  | 17 => .thirtyOne
  | 18 => .thirtyOne
  | 19 => .thirtyOne
  | 20 => .thirtyOne
  | 21 => .general ⟨0,by decide⟩
  | 22 => .general ⟨0,by decide⟩
  | _ => .thirtyOne

theorem scalar_valid : ScalarValid ⟨32,by decide⟩ parameters theta ratioMax reverse profiles := by
  constructor
  all_goals try norm_num [parameters,theta,ratioMax,reverse,Stage350SourceTable.row]
  · intro j hj;interval_cases j <;> norm_num [profiles,Stage900DirectionInputs.ProfileRange,
      Stage350SourceTable.row,parameters,JointDirectionSmallCost.cuts,BinomialGradientTable.scale]
  · intro j hj;interval_cases j <;> norm_num [profiles,GradientProfile.constant,
      BinomialGradientTable.generalConstant,BinomialGradientTable.nearConstant,parameters,smallCoefficient]

theorem envelope_valid : JointDirectionActual.Envelope parameters theta := by
  constructor
  · have h:=@GaussianDirectionalCatalogue.interpolated_envelope ⟨1,by decide⟩ ⟨2,by decide⟩ (227677/625000) (by norm_num) (by norm_num)
    norm_num [GaussianDirectionalCatalogue.thetaMax,GaussianDirectionalCatalogue.xQuadratic,
      GaussianDirectionalCatalogue.yQuadratic,GaussianDirectionalCatalogue.parameters] at h
    exact @h
  all_goals norm_num [parameters,theta,GaussianDirectionalFamily.badPrice]

variable {V:Type*} [DecidableEq V]

theorem small_tail {G:SimpleGraph V} {S B:Finset V} {z:ℝ}
    (hB:IsMaximumMarginalIndependentOn G S B z) (hG:G.IsAcyclic) (hn:0<S.card)
    (hlo:((Stage350SourceTable.row ⟨32,by decide⟩).a:ℝ)≤z)
    (hhi:z≤((Stage350SourceTable.row ⟨32,by decide⟩).b:ℝ))
    (hrank:(S.card:ℝ)/4≤hardCoreMean G S z)
    (j:ℕ) (hj:j<24) :
    hardCoreAvailableLowerTail G S B z (JointDirectionSmallCost.cuts (hardCoreAvailableMean G S B z) j)≤
      exp (-parameters.smallRate j*hardCoreAvailableMean G S B z) := by
  interval_cases j
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail00.source
      (α:=Tail00.cut) (u:=Tail00.tilt) (rate:=Tail00.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail00.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail00.cut]) (by norm_num [Tail00.tilt]) Tail00.rate_valid
    convert! h using 1
    all_goals norm_num [Tail00.cut,Tail00.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail01.source
      (α:=Tail01.cut) (u:=Tail01.tilt) (rate:=Tail01.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail01.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail01.cut]) (by norm_num [Tail01.tilt]) Tail01.rate_valid
    convert! h using 1
    all_goals norm_num [Tail01.cut,Tail01.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail02.source
      (α:=Tail02.cut) (u:=Tail02.tilt) (rate:=Tail02.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail02.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail02.cut]) (by norm_num [Tail02.tilt]) Tail02.rate_valid
    convert! h using 1
    all_goals norm_num [Tail02.cut,Tail02.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail03.source
      (α:=Tail03.cut) (u:=Tail03.tilt) (rate:=Tail03.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail03.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail03.cut]) (by norm_num [Tail03.tilt]) Tail03.rate_valid
    convert! h using 1
    all_goals norm_num [Tail03.cut,Tail03.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail04.source
      (α:=Tail04.cut) (u:=Tail04.tilt) (rate:=Tail04.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail04.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail04.cut]) (by norm_num [Tail04.tilt]) Tail04.rate_valid
    convert! h using 1
    all_goals norm_num [Tail04.cut,Tail04.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail05.source
      (α:=Tail05.cut) (u:=Tail05.tilt) (rate:=Tail05.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail05.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail05.cut]) (by norm_num [Tail05.tilt]) Tail05.rate_valid
    convert! h using 1
    all_goals norm_num [Tail05.cut,Tail05.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail06.source
      (α:=Tail06.cut) (u:=Tail06.tilt) (rate:=Tail06.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail06.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail06.cut]) (by norm_num [Tail06.tilt]) Tail06.rate_valid
    convert! h using 1
    all_goals norm_num [Tail06.cut,Tail06.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail07.source
      (α:=Tail07.cut) (u:=Tail07.tilt) (rate:=Tail07.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail07.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail07.cut]) (by norm_num [Tail07.tilt]) Tail07.rate_valid
    convert! h using 1
    all_goals norm_num [Tail07.cut,Tail07.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail08.source
      (α:=Tail08.cut) (u:=Tail08.tilt) (rate:=Tail08.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail08.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail08.cut]) (by norm_num [Tail08.tilt]) Tail08.rate_valid
    convert! h using 1
    all_goals norm_num [Tail08.cut,Tail08.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail09.source
      (α:=Tail09.cut) (u:=Tail09.tilt) (rate:=Tail09.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail09.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail09.cut]) (by norm_num [Tail09.tilt]) Tail09.rate_valid
    convert! h using 1
    all_goals norm_num [Tail09.cut,Tail09.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail10.source
      (α:=Tail10.cut) (u:=Tail10.tilt) (rate:=Tail10.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail10.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail10.cut]) (by norm_num [Tail10.tilt]) Tail10.rate_valid
    convert! h using 1
    all_goals norm_num [Tail10.cut,Tail10.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail11.source
      (α:=Tail11.cut) (u:=Tail11.tilt) (rate:=Tail11.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail11.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail11.cut]) (by norm_num [Tail11.tilt]) Tail11.rate_valid
    convert! h using 1
    all_goals norm_num [Tail11.cut,Tail11.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail12.source
      (α:=Tail12.cut) (u:=Tail12.tilt) (rate:=Tail12.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail12.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail12.cut]) (by norm_num [Tail12.tilt]) Tail12.rate_valid
    convert! h using 1
    all_goals norm_num [Tail12.cut,Tail12.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail13.source
      (α:=Tail13.cut) (u:=Tail13.tilt) (rate:=Tail13.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail13.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail13.cut]) (by norm_num [Tail13.tilt]) Tail13.rate_valid
    convert! h using 1
    all_goals norm_num [Tail13.cut,Tail13.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail14.source
      (α:=Tail14.cut) (u:=Tail14.tilt) (rate:=Tail14.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail14.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail14.cut]) (by norm_num [Tail14.tilt]) Tail14.rate_valid
    convert! h using 1
    all_goals norm_num [Tail14.cut,Tail14.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail15.source
      (α:=Tail15.cut) (u:=Tail15.tilt) (rate:=Tail15.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail15.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail15.cut]) (by norm_num [Tail15.tilt]) Tail15.rate_valid
    convert! h using 1
    all_goals norm_num [Tail15.cut,Tail15.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail16.source
      (α:=Tail16.cut) (u:=Tail16.tilt) (rate:=Tail16.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail16.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail16.cut]) (by norm_num [Tail16.tilt]) Tail16.rate_valid
    convert! h using 1
    all_goals norm_num [Tail16.cut,Tail16.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail17.source
      (α:=Tail17.cut) (u:=Tail17.tilt) (rate:=Tail17.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail17.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail17.cut]) (by norm_num [Tail17.tilt]) Tail17.rate_valid
    convert! h using 1
    all_goals norm_num [Tail17.cut,Tail17.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail18.source
      (α:=Tail18.cut) (u:=Tail18.tilt) (rate:=Tail18.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail18.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail18.cut]) (by norm_num [Tail18.tilt]) Tail18.rate_valid
    convert! h using 1
    all_goals norm_num [Tail18.cut,Tail18.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail19.source
      (α:=Tail19.cut) (u:=Tail19.tilt) (rate:=Tail19.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail19.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail19.cut]) (by norm_num [Tail19.tilt]) Tail19.rate_valid
    convert! h using 1
    all_goals norm_num [Tail19.cut,Tail19.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail20.source
      (α:=Tail20.cut) (u:=Tail20.tilt) (rate:=Tail20.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail20.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail20.cut]) (by norm_num [Tail20.tilt]) Tail20.rate_valid
    convert! h using 1
    all_goals norm_num [Tail20.cut,Tail20.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail21.source
      (α:=Tail21.cut) (u:=Tail21.tilt) (rate:=Tail21.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail21.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail21.cut]) (by norm_num [Tail21.tilt]) Tail21.rate_valid
    convert! h using 1
    all_goals norm_num [Tail21.cut,Tail21.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail22.source
      (α:=Tail22.cut) (u:=Tail22.tilt) (rate:=Tail22.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail22.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail22.cut]) (by norm_num [Tail22.tilt]) Tail22.rate_valid
    convert! h using 1
    all_goals norm_num [Tail22.cut,Tail22.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail23.source
      (α:=Tail23.cut) (u:=Tail23.tilt) (rate:=Tail23.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail23.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail23.cut]) (by norm_num [Tail23.tilt]) Tail23.rate_valid
    convert! h using 1
    all_goals norm_num [Tail23.cut,Tail23.rate,parameters,smallRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]

theorem profile_tail {G:SimpleGraph V} {S B:Finset V} {z:ℝ}
    (hB:IsMaximumMarginalIndependentOn G S B z) (hG:G.IsAcyclic) (hn:0<S.card)
    (hlo:((Stage350SourceTable.row ⟨32,by decide⟩).a:ℝ)≤z)
    (hhi:z≤((Stage350SourceTable.row ⟨32,by decide⟩).b:ℝ))
    (hrank:(S.card:ℝ)/4≤hardCoreMean G S z)
    (j:ℕ) (hj:j<40) :
    hardCoreAvailableLowerTail G S B z (SignedGaussian350JointData.AlphaFourNinthBeta65.cuts (j+1)*hardCoreAvailableMean G S B z)≤
      exp (-parameters.profileRate j*hardCoreAvailableMean G S B z) := by
  interval_cases j
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail24.source
      (α:=Tail24.cut) (u:=Tail24.tilt) (rate:=Tail24.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail24.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail24.cut]) (by norm_num [Tail24.tilt]) Tail24.rate_valid
    convert! h using 1
    all_goals norm_num [Tail24.cut,Tail24.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail25.source
      (α:=Tail25.cut) (u:=Tail25.tilt) (rate:=Tail25.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail25.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail25.cut]) (by norm_num [Tail25.tilt]) Tail25.rate_valid
    convert! h using 1
    all_goals norm_num [Tail25.cut,Tail25.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail26.source
      (α:=Tail26.cut) (u:=Tail26.tilt) (rate:=Tail26.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail26.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail26.cut]) (by norm_num [Tail26.tilt]) Tail26.rate_valid
    convert! h using 1
    all_goals norm_num [Tail26.cut,Tail26.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail27.source
      (α:=Tail27.cut) (u:=Tail27.tilt) (rate:=Tail27.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail27.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail27.cut]) (by norm_num [Tail27.tilt]) Tail27.rate_valid
    convert! h using 1
    all_goals norm_num [Tail27.cut,Tail27.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail28.source
      (α:=Tail28.cut) (u:=Tail28.tilt) (rate:=Tail28.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail28.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail28.cut]) (by norm_num [Tail28.tilt]) Tail28.rate_valid
    convert! h using 1
    all_goals norm_num [Tail28.cut,Tail28.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail29.source
      (α:=Tail29.cut) (u:=Tail29.tilt) (rate:=Tail29.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail29.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail29.cut]) (by norm_num [Tail29.tilt]) Tail29.rate_valid
    convert! h using 1
    all_goals norm_num [Tail29.cut,Tail29.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail30.source
      (α:=Tail30.cut) (u:=Tail30.tilt) (rate:=Tail30.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail30.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail30.cut]) (by norm_num [Tail30.tilt]) Tail30.rate_valid
    convert! h using 1
    all_goals norm_num [Tail30.cut,Tail30.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail31.source
      (α:=Tail31.cut) (u:=Tail31.tilt) (rate:=Tail31.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail31.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail31.cut]) (by norm_num [Tail31.tilt]) Tail31.rate_valid
    convert! h using 1
    all_goals norm_num [Tail31.cut,Tail31.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail32.source
      (α:=Tail32.cut) (u:=Tail32.tilt) (rate:=Tail32.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail32.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail32.cut]) (by norm_num [Tail32.tilt]) Tail32.rate_valid
    convert! h using 1
    all_goals norm_num [Tail32.cut,Tail32.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail33.source
      (α:=Tail33.cut) (u:=Tail33.tilt) (rate:=Tail33.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail33.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail33.cut]) (by norm_num [Tail33.tilt]) Tail33.rate_valid
    convert! h using 1
    all_goals norm_num [Tail33.cut,Tail33.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail34.source
      (α:=Tail34.cut) (u:=Tail34.tilt) (rate:=Tail34.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail34.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail34.cut]) (by norm_num [Tail34.tilt]) Tail34.rate_valid
    convert! h using 1
    all_goals norm_num [Tail34.cut,Tail34.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail35.source
      (α:=Tail35.cut) (u:=Tail35.tilt) (rate:=Tail35.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail35.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail35.cut]) (by norm_num [Tail35.tilt]) Tail35.rate_valid
    convert! h using 1
    all_goals norm_num [Tail35.cut,Tail35.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail36.source
      (α:=Tail36.cut) (u:=Tail36.tilt) (rate:=Tail36.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail36.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail36.cut]) (by norm_num [Tail36.tilt]) Tail36.rate_valid
    convert! h using 1
    all_goals norm_num [Tail36.cut,Tail36.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail37.source
      (α:=Tail37.cut) (u:=Tail37.tilt) (rate:=Tail37.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail37.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail37.cut]) (by norm_num [Tail37.tilt]) Tail37.rate_valid
    convert! h using 1
    all_goals norm_num [Tail37.cut,Tail37.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail38.source
      (α:=Tail38.cut) (u:=Tail38.tilt) (rate:=Tail38.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail38.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail38.cut]) (by norm_num [Tail38.tilt]) Tail38.rate_valid
    convert! h using 1
    all_goals norm_num [Tail38.cut,Tail38.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail39.source
      (α:=Tail39.cut) (u:=Tail39.tilt) (rate:=Tail39.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail39.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail39.cut]) (by norm_num [Tail39.tilt]) Tail39.rate_valid
    convert! h using 1
    all_goals norm_num [Tail39.cut,Tail39.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail40.source
      (α:=Tail40.cut) (u:=Tail40.tilt) (rate:=Tail40.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail40.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail40.cut]) (by norm_num [Tail40.tilt]) Tail40.rate_valid
    convert! h using 1
    all_goals norm_num [Tail40.cut,Tail40.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail41.source
      (α:=Tail41.cut) (u:=Tail41.tilt) (rate:=Tail41.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail41.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail41.cut]) (by norm_num [Tail41.tilt]) Tail41.rate_valid
    convert! h using 1
    all_goals norm_num [Tail41.cut,Tail41.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail42.source
      (α:=Tail42.cut) (u:=Tail42.tilt) (rate:=Tail42.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail42.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail42.cut]) (by norm_num [Tail42.tilt]) Tail42.rate_valid
    convert! h using 1
    all_goals norm_num [Tail42.cut,Tail42.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail43.source
      (α:=Tail43.cut) (u:=Tail43.tilt) (rate:=Tail43.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail43.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail43.cut]) (by norm_num [Tail43.tilt]) Tail43.rate_valid
    convert! h using 1
    all_goals norm_num [Tail43.cut,Tail43.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail44.source
      (α:=Tail44.cut) (u:=Tail44.tilt) (rate:=Tail44.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail44.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail44.cut]) (by norm_num [Tail44.tilt]) Tail44.rate_valid
    convert! h using 1
    all_goals norm_num [Tail44.cut,Tail44.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail45.source
      (α:=Tail45.cut) (u:=Tail45.tilt) (rate:=Tail45.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail45.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail45.cut]) (by norm_num [Tail45.tilt]) Tail45.rate_valid
    convert! h using 1
    all_goals norm_num [Tail45.cut,Tail45.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail46.source
      (α:=Tail46.cut) (u:=Tail46.tilt) (rate:=Tail46.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail46.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail46.cut]) (by norm_num [Tail46.tilt]) Tail46.rate_valid
    convert! h using 1
    all_goals norm_num [Tail46.cut,Tail46.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail47.source
      (α:=Tail47.cut) (u:=Tail47.tilt) (rate:=Tail47.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail47.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail47.cut]) (by norm_num [Tail47.tilt]) Tail47.rate_valid
    convert! h using 1
    all_goals norm_num [Tail47.cut,Tail47.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail48.source
      (α:=Tail48.cut) (u:=Tail48.tilt) (rate:=Tail48.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail48.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail48.cut]) (by norm_num [Tail48.tilt]) Tail48.rate_valid
    convert! h using 1
    all_goals norm_num [Tail48.cut,Tail48.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail49.source
      (α:=Tail49.cut) (u:=Tail49.tilt) (rate:=Tail49.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail49.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail49.cut]) (by norm_num [Tail49.tilt]) Tail49.rate_valid
    convert! h using 1
    all_goals norm_num [Tail49.cut,Tail49.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail50.source
      (α:=Tail50.cut) (u:=Tail50.tilt) (rate:=Tail50.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail50.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail50.cut]) (by norm_num [Tail50.tilt]) Tail50.rate_valid
    convert! h using 1
    all_goals norm_num [Tail50.cut,Tail50.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail51.source
      (α:=Tail51.cut) (u:=Tail51.tilt) (rate:=Tail51.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail51.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail51.cut]) (by norm_num [Tail51.tilt]) Tail51.rate_valid
    convert! h using 1
    all_goals norm_num [Tail51.cut,Tail51.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail52.source
      (α:=Tail52.cut) (u:=Tail52.tilt) (rate:=Tail52.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail52.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail52.cut]) (by norm_num [Tail52.tilt]) Tail52.rate_valid
    convert! h using 1
    all_goals norm_num [Tail52.cut,Tail52.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail53.source
      (α:=Tail53.cut) (u:=Tail53.tilt) (rate:=Tail53.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail53.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail53.cut]) (by norm_num [Tail53.tilt]) Tail53.rate_valid
    convert! h using 1
    all_goals norm_num [Tail53.cut,Tail53.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail54.source
      (α:=Tail54.cut) (u:=Tail54.tilt) (rate:=Tail54.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail54.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail54.cut]) (by norm_num [Tail54.tilt]) Tail54.rate_valid
    convert! h using 1
    all_goals norm_num [Tail54.cut,Tail54.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail55.source
      (α:=Tail55.cut) (u:=Tail55.tilt) (rate:=Tail55.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail55.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail55.cut]) (by norm_num [Tail55.tilt]) Tail55.rate_valid
    convert! h using 1
    all_goals norm_num [Tail55.cut,Tail55.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail56.source
      (α:=Tail56.cut) (u:=Tail56.tilt) (rate:=Tail56.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail56.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail56.cut]) (by norm_num [Tail56.tilt]) Tail56.rate_valid
    convert! h using 1
    all_goals norm_num [Tail56.cut,Tail56.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail57.source
      (α:=Tail57.cut) (u:=Tail57.tilt) (rate:=Tail57.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail57.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail57.cut]) (by norm_num [Tail57.tilt]) Tail57.rate_valid
    convert! h using 1
    all_goals norm_num [Tail57.cut,Tail57.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail58.source
      (α:=Tail58.cut) (u:=Tail58.tilt) (rate:=Tail58.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail58.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail58.cut]) (by norm_num [Tail58.tilt]) Tail58.rate_valid
    convert! h using 1
    all_goals norm_num [Tail58.cut,Tail58.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail59.source
      (α:=Tail59.cut) (u:=Tail59.tilt) (rate:=Tail59.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail59.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail59.cut]) (by norm_num [Tail59.tilt]) Tail59.rate_valid
    convert! h using 1
    all_goals norm_num [Tail59.cut,Tail59.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail60.source
      (α:=Tail60.cut) (u:=Tail60.tilt) (rate:=Tail60.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail60.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail60.cut]) (by norm_num [Tail60.tilt]) Tail60.rate_valid
    convert! h using 1
    all_goals norm_num [Tail60.cut,Tail60.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail61.source
      (α:=Tail61.cut) (u:=Tail61.tilt) (rate:=Tail61.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail61.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail61.cut]) (by norm_num [Tail61.tilt]) Tail61.rate_valid
    convert! h using 1
    all_goals norm_num [Tail61.cut,Tail61.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail62.source
      (α:=Tail62.cut) (u:=Tail62.tilt) (rate:=Tail62.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail62.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail62.cut]) (by norm_num [Tail62.tilt]) Tail62.rate_valid
    convert! h using 1
    all_goals norm_num [Tail62.cut,Tail62.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]
  · have h:=Stage350AffineTailAllOrders.actual_affine_tail_le_rate ⟨32,by decide⟩ Tail63.source
      (α:=Tail63.cut) (u:=Tail63.tilt) (rate:=Tail63.rate) hB hG hn hlo hhi hrank
      (by norm_num [Stage350SourceTable.row,Tail63.source,AffineSourceLibrary.domain,AffineSourceData.Case14.domain])
      (by norm_num [Tail63.cut]) (by norm_num [Tail63.tilt]) Tail63.rate_valid
    convert! h using 1
    all_goals norm_num [Tail63.cut,Tail63.rate,parameters,profileRate,JointDirectionSmallCost.cuts,
      SignedGaussian350JointData.AlphaFourNinthBeta65.cuts,SignedGaussian350JointData.AlphaFourNinthBeta65.beta]

theorem actual_inputs {G:SimpleGraph V} {S B:Finset V} {z:ℝ} (k:ℕ)
    (hB:IsMaximumMarginalIndependentOn G S B z) (hG:G.IsAcyclic) (hn:0<S.card)
    (hs:parameters.start≤hardCoreAvailableMean G S B z)
    (hlo:((Stage350SourceTable.row ⟨32,by decide⟩).a:ℝ)≤z)
    (hhi:z≤((Stage350SourceTable.row ⟨32,by decide⟩).b:ℝ))
    (hrank:(S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean:hardCoreMean G S z=k) :
    JointDirectionActual.Inputs parameters G S B z (hardCoreAvailableMean G S B z)
      (Stage350JointInputs.ratio reverse z) theta k reverse profiles :=
  actual_inputs_of_start ⟨32,by decide⟩ parameters parameters_valid theta ratioMax reverse profiles scalar_valid
    k hB hG hn hs hlo hhi hrank hmean (profile_tail hB hG hn hlo hhi hrank) (small_tail hB hG hn hlo hhi hrank)

#print axioms scalar_valid
#print axioms envelope_valid
#print axioms actual_inputs
end ForestUnimodality.Stage350JointInputsData.Case33
