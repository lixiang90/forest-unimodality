import ForestUnimodality.Stage350CurvatureAllOrders
import ForestUnimodality.Stage350CurvatureData.Case18
import ForestUnimodality.Stage350CurvatureTails.Case18.Part00
import ForestUnimodality.Stage350CurvatureTails.Case18.Part01
import ForestUnimodality.Stage350CurvatureTails.Case18.Part02
import ForestUnimodality.Stage350CurvatureTails.Case18.Part03
import ForestUnimodality.Stage350CurvatureTails.Case18.Part04
import ForestUnimodality.Stage350CurvatureTails.Case18.Part05
import ForestUnimodality.Stage350CurvatureTails.Case18.Part06
import ForestUnimodality.Stage350CurvatureTails.Case18.Part07

namespace ForestUnimodality.Stage350CurvatureInputsData.Case18
open Stage350CurvatureInputs Stage350CurvatureBudget Stage350CurvatureData.Case18
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem scalar_valid : ScalarValid ⟨17,by decide⟩ parameters := by
  constructor <;> norm_num [parameters,Stage350SourceTable.row,qLower,qUpper]

theorem gapVerified_exists (j : Fin 40) :
    Nonempty (Stage350VerifiedTail.Verified ⟨17,by decide⟩ (profileCut parameters.largeBeta (j.val+1)) (parameters.gapRate j)) := by
  fin_cases j
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail00 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail01 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail02 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail03 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail04 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail05 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail06 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail07 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail08 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail09 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail10 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail11 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail12 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail13 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail14 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail15 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail16 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail17 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail18 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail19 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail20 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail21 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail22 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail23 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail24 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail25 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail26 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail27 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail28 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail29 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail30 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail31 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail32 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail33 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail34 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail35 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail36 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail37 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail38 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail39 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]

noncomputable def gapVerified (j : Fin 40) :
    Stage350VerifiedTail.Verified ⟨17,by decide⟩ (profileCut parameters.largeBeta (j.val+1)) (parameters.gapRate j) :=
  Classical.choice (gapVerified_exists j)

theorem badVerified_exists (j : Fin 24) :
    Nonempty (Stage350VerifiedTail.Verified ⟨17,by decide⟩ (cut j.val) (parameters.badRate j)) := by
  fin_cases j
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail40 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail41 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail42 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail43 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail44 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail45 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail46 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail47 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail48 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail49 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail50 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail51 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail52 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail53 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail54 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail55 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail56 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail57 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail58 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail59 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail60 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail61 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail62 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]
  · refine ⟨?_⟩
    convert Stage350CurvatureTails.Case18.tail63 using 1 <;>
      norm_num [parameters,gapRates,badRates,profileCut,beta,cut,
        SignedGaussian350Data.Beta60.beta,SignedGaussian350Data.Beta65.beta]

noncomputable def badVerified (j : Fin 24) :
    Stage350VerifiedTail.Verified ⟨17,by decide⟩ (cut j.val) (parameters.badRate j) :=
  Classical.choice (badVerified_exists j)

variable {V : Type*} [DecidableEq V]

theorem actual_inputs {G : SimpleGraph V} {S I : Finset V} {z : ℝ} (k : ℕ)
    (hI : IsMaximumMarginalIndependentOn G S I z) (hG : G.IsAcyclic)
    (hn : 350≤S.card) (hz : z∈Set.Icc parameters.a parameters.b)
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=(k:ℝ)) :
    Stage350CurvatureGraph.Inputs parameters G S I z (hardCoreAvailableMean G S I z) k :=
  Stage350CurvatureInputs.actual_inputs ⟨17,by decide⟩ parameters scalar_valid gapVerified badVerified
    k hI hG hn hz hrank hmean

theorem actual_inputs_any_size {G : SimpleGraph V} {S I : Finset V} {z : ℝ} (k : ℕ)
    (hI : IsMaximumMarginalIndependentOn G S I z) (hG : G.IsAcyclic)
    (hn : 0<S.card) (hz : z∈Set.Icc parameters.a parameters.b)
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=(k:ℝ))
    (hstart : parameters.start≤hardCoreAvailableMean G S I z) :
    Stage350CurvatureGraph.Inputs parameters G S I z (hardCoreAvailableMean G S I z) k :=
  Stage350CurvatureInputs.actual_inputs_any_size ⟨17,by decide⟩ parameters scalar_valid gapVerified badVerified
    k hI hG hn hz hrank hmean hstart

#print axioms scalar_valid
#print axioms actual_inputs
#print axioms actual_inputs_any_size
end ForestUnimodality.Stage350CurvatureInputsData.Case18
