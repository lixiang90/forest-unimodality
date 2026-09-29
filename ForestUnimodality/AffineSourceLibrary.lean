import ForestUnimodality.AffineSourceData.Case01.Complete
import ForestUnimodality.AffineSourceData.Case02.Complete
import ForestUnimodality.AffineSourceData.Case03.Complete
import ForestUnimodality.AffineSourceData.Case04.Complete
import ForestUnimodality.AffineSourceData.Case05.Complete
import ForestUnimodality.AffineSourceData.Case06.Complete
import ForestUnimodality.AffineSourceData.Case07.Complete
import ForestUnimodality.AffineSourceData.Case08.Complete
import ForestUnimodality.AffineSourceData.Case09.Complete
import ForestUnimodality.AffineSourceData.Case10.Complete
import ForestUnimodality.AffineSourceData.Case11.Complete
import ForestUnimodality.AffineSourceData.Case12.Complete
import ForestUnimodality.AffineSourceData.Case13.Complete
import ForestUnimodality.AffineSourceData.Case14.Complete
import ForestUnimodality.AffineSourceData.Case15.Complete

/-! Fifteen certified support-size affine sources. The activity cap is only
an upper bound: all strictly positive smaller activities remain admissible. -/
namespace ForestUnimodality.AffineSourceLibrary

def parameters (i : Fin 15) : AffineSource.Parameters :=
  ![AffineSourceData.Case01.parameters, AffineSourceData.Case02.parameters, AffineSourceData.Case03.parameters, AffineSourceData.Case04.parameters, AffineSourceData.Case05.parameters, AffineSourceData.Case06.parameters, AffineSourceData.Case07.parameters, AffineSourceData.Case08.parameters, AffineSourceData.Case09.parameters, AffineSourceData.Case10.parameters, AffineSourceData.Case11.parameters, AffineSourceData.Case12.parameters, AffineSourceData.Case13.parameters, AffineSourceData.Case14.parameters, AffineSourceData.Case15.parameters] i

def domain (i : Fin 15) : AffineSource.Domain :=
  ![AffineSourceData.Case01.domain, AffineSourceData.Case02.domain, AffineSourceData.Case03.domain, AffineSourceData.Case04.domain, AffineSourceData.Case05.domain, AffineSourceData.Case06.domain, AffineSourceData.Case07.domain, AffineSourceData.Case08.domain, AffineSourceData.Case09.domain, AffineSourceData.Case10.domain, AffineSourceData.Case11.domain, AffineSourceData.Case12.domain, AffineSourceData.Case13.domain, AffineSourceData.Case14.domain, AffineSourceData.Case15.domain] i

theorem parameters_checked (i : Fin 15) : (parameters i).check=true := by
  fin_cases i
  · exact AffineSourceData.Case01.parameters_checked
  · exact AffineSourceData.Case02.parameters_checked
  · exact AffineSourceData.Case03.parameters_checked
  · exact AffineSourceData.Case04.parameters_checked
  · exact AffineSourceData.Case05.parameters_checked
  · exact AffineSourceData.Case06.parameters_checked
  · exact AffineSourceData.Case07.parameters_checked
  · exact AffineSourceData.Case08.parameters_checked
  · exact AffineSourceData.Case09.parameters_checked
  · exact AffineSourceData.Case10.parameters_checked
  · exact AffineSourceData.Case11.parameters_checked
  · exact AffineSourceData.Case12.parameters_checked
  · exact AffineSourceData.Case13.parameters_checked
  · exact AffineSourceData.Case14.parameters_checked
  · exact AffineSourceData.Case15.parameters_checked

theorem domain_checked (i : Fin 15) : (domain i).check=true := by
  fin_cases i
  · exact AffineSourceData.Case01.domain_checked
  · exact AffineSourceData.Case02.domain_checked
  · exact AffineSourceData.Case03.domain_checked
  · exact AffineSourceData.Case04.domain_checked
  · exact AffineSourceData.Case05.domain_checked
  · exact AffineSourceData.Case06.domain_checked
  · exact AffineSourceData.Case07.domain_checked
  · exact AffineSourceData.Case08.domain_checked
  · exact AffineSourceData.Case09.domain_checked
  · exact AffineSourceData.Case10.domain_checked
  · exact AffineSourceData.Case11.domain_checked
  · exact AffineSourceData.Case12.domain_checked
  · exact AffineSourceData.Case13.domain_checked
  · exact AffineSourceData.Case14.domain_checked
  · exact AffineSourceData.Case15.domain_checked

theorem source_valid (i : Fin 15) :
    AffineSourceRowValid (parameters i).toReal (domain i).b := by
  fin_cases i
  · exact AffineSourceData.Case01.source_valid
  · exact AffineSourceData.Case02.source_valid
  · exact AffineSourceData.Case03.source_valid
  · exact AffineSourceData.Case04.source_valid
  · exact AffineSourceData.Case05.source_valid
  · exact AffineSourceData.Case06.source_valid
  · exact AffineSourceData.Case07.source_valid
  · exact AffineSourceData.Case08.source_valid
  · exact AffineSourceData.Case09.source_valid
  · exact AffineSourceData.Case10.source_valid
  · exact AffineSourceData.Case11.source_valid
  · exact AffineSourceData.Case12.source_valid
  · exact AffineSourceData.Case13.source_valid
  · exact AffineSourceData.Case14.source_valid
  · exact AffineSourceData.Case15.source_valid

theorem C_pos (i : Fin 15) : (0:ℝ)<(parameters i).C := by
  fin_cases i <;> norm_num [parameters,
    AffineSourceData.Case01.parameters,
    AffineSourceData.Case02.parameters,
    AffineSourceData.Case03.parameters,
    AffineSourceData.Case04.parameters,
    AffineSourceData.Case05.parameters,
    AffineSourceData.Case06.parameters,
    AffineSourceData.Case07.parameters,
    AffineSourceData.Case08.parameters,
    AffineSourceData.Case09.parameters,
    AffineSourceData.Case10.parameters,
    AffineSourceData.Case11.parameters,
    AffineSourceData.Case12.parameters,
    AffineSourceData.Case13.parameters,
    AffineSourceData.Case14.parameters,
    AffineSourceData.Case15.parameters]

variable {V : Type*} [DecidableEq V]

theorem actual_tilt (i : Fin 15) (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S B : Finset V) (hBS : B⊆S) {z : ℝ}
    (hz : 0<z) (hzb : z≤((domain i).b:ℝ)) :
    ∀t≥0, heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
      (fun J=>((J∩B).card:ℝ)) ≤
      (parameters i).A*(B.card:ℝ)+(parameters i).C*
        heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t)))
          (fun J=>((J∩B).card:ℝ)) :=
  forest_marked_affine_source_tilt G hG S B hBS hz hzb (parameters i).toReal
    (AffineSource.Parameters.check_sound (parameters_checked i)).1 (source_valid i)

theorem actual_tail_of_endpoints (i : Fin 15)
    {G : SimpleGraph V} {S B : Finset V} {z ρ α u rate lo hi : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hzb : z≤((domain i).b:ℝ)) (hρ : 0<ρ) (hρq : ρ≤z/(1+z))
    (hu : 0≤u) (hα : 0≤α)
    (hdensity : ρ*(S.card:ℝ)≤hardCoreMean G S z)
    (hlo : 0≤lo) (hhi : hi≤1) (hq : z/(1+z)∈Set.Icc lo hi)
    (hrlo : rate≤AffineLaplace.tailRate (parameters i).A (parameters i).C ρ α u lo)
    (hrhi : rate≤AffineLaplace.tailRate (parameters i).A (parameters i).C ρ α u hi) :
    hardCoreAvailableLowerTail G S B z (α*hardCoreAvailableMean G S B z) ≤
      Real.exp (-rate*hardCoreAvailableMean G S B z) := by
  have hP := AffineSource.Parameters.check_sound (parameters_checked i)
  exact hB.lowerTail_le_affine_source_certificate hG hz hzb hρ hρq
    (parameters i).toReal hP.1 (source_valid i) hP.2.1 (C_pos i) hu hα hdensity
    hlo hhi hq hrlo hrhi

#print axioms source_valid
#print axioms actual_tilt
#print axioms actual_tail_of_endpoints
end ForestUnimodality.AffineSourceLibrary

