import ForestUnimodality.SharedAffineData.EarlyStop20260928.Common
import ForestUnimodality.Stage170SourceData.Windows.Batch060_079

namespace ForestUnimodality.SharedAffineData.EarlyStop20260928
open SharedAffineLaplace
set_option maxRecDepth 100000
set_option maxHeartbeats 0
variable {V : Type*} [DecidableEq V]

namespace Stage130Cell236Term01
def rate : ℚ := (117202945087834829656618761841/1000000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window072.window.rho Tilt00.u Stage170SourceData.Window072.window.qa rate Decay00.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window072.window.rho Tilt00.u Stage170SourceData.Window072.window.qb rate Decay00.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window072.window.qa:ℝ) (Stage170SourceData.Window072.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window072.window.upper:ℝ)≤(AffineSourceLibrary.domain (14:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window072.window.upper≤(AffineSourceLibrary.domain (14:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (14:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window072.valid.qb_lt_one.le
    Tilt00.retention_bound Decay00.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window072.window.activity_bounds Stage170SourceData.Window072.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window072.window.density Stage170SourceData.Window072.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell236Term01

namespace Stage130Cell237Term01
def rate : ℚ := (118936770211060555194686002293/1000000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window073.window.rho Tilt00.u Stage170SourceData.Window073.window.qa rate Decay00.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window073.window.rho Tilt00.u Stage170SourceData.Window073.window.qb rate Decay00.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window073.window.qa:ℝ) (Stage170SourceData.Window073.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window073.window.upper:ℝ)≤(AffineSourceLibrary.domain (14:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window073.window.upper≤(AffineSourceLibrary.domain (14:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (14:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window073.valid.qb_lt_one.le
    Tilt00.retention_bound Decay00.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window073.window.activity_bounds Stage170SourceData.Window073.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window073.window.density Stage170SourceData.Window073.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell237Term01

namespace Stage130Cell238Term01
def rate : ℚ := (120673627134489075602089476257/1000000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window074.window.rho Tilt00.u Stage170SourceData.Window074.window.qa rate Decay00.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window074.window.rho Tilt00.u Stage170SourceData.Window074.window.qb rate Decay00.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window074.window.qa:ℝ) (Stage170SourceData.Window074.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window074.window.upper:ℝ)≤(AffineSourceLibrary.domain (14:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window074.window.upper≤(AffineSourceLibrary.domain (14:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (14:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window074.valid.qb_lt_one.le
    Tilt00.retention_bound Decay00.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window074.window.activity_bounds Stage170SourceData.Window074.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window074.window.density Stage170SourceData.Window074.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell238Term01

namespace Stage130Cell239Term01
def rate : ℚ := (61304787699704703640566705149/500000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window075.window.rho Tilt00.u Stage170SourceData.Window075.window.qa rate Decay00.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window075.window.rho Tilt00.u Stage170SourceData.Window075.window.qb rate Decay00.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window075.window.qa:ℝ) (Stage170SourceData.Window075.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window075.window.upper:ℝ)≤(AffineSourceLibrary.domain (14:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window075.window.upper≤(AffineSourceLibrary.domain (14:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (14:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window075.valid.qb_lt_one.le
    Tilt00.retention_bound Decay00.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window075.window.activity_bounds Stage170SourceData.Window075.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window075.window.density Stage170SourceData.Window075.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell239Term01

namespace Stage130Cell240Term01
def rate : ℚ := (7751001877292346530475136499/62500000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window076.window.rho Tilt00.u Stage170SourceData.Window076.window.qa rate Decay00.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window076.window.rho Tilt00.u Stage170SourceData.Window076.window.qb rate Decay00.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window076.window.qa:ℝ) (Stage170SourceData.Window076.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window076.window.upper:ℝ)≤(AffineSourceLibrary.domain (14:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window076.window.upper≤(AffineSourceLibrary.domain (14:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (14:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window076.valid.qb_lt_one.le
    Tilt00.retention_bound Decay00.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window076.window.activity_bounds Stage170SourceData.Window076.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window076.window.density Stage170SourceData.Window076.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell240Term01

namespace Stage130Cell241Term01
def rate : ℚ := (125424380727847080726155368493/1000000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window077.window.rho Tilt00.u Stage170SourceData.Window077.window.qa rate Decay00.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window077.window.rho Tilt00.u Stage170SourceData.Window077.window.qb rate Decay00.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window077.window.qa:ℝ) (Stage170SourceData.Window077.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window077.window.upper:ℝ)≤(AffineSourceLibrary.domain (14:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window077.window.upper≤(AffineSourceLibrary.domain (14:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (14:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window077.valid.qb_lt_one.le
    Tilt00.retention_bound Decay00.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window077.window.activity_bounds Stage170SourceData.Window077.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window077.window.density Stage170SourceData.Window077.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell241Term01

namespace Stage130Cell242Term01
def rate : ℚ := (6341730061154019367291076197/50000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window078.window.rho Tilt00.u Stage170SourceData.Window078.window.qa rate Decay00.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window078.window.rho Tilt00.u Stage170SourceData.Window078.window.qb rate Decay00.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window078.window.qa:ℝ) (Stage170SourceData.Window078.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window078.window.upper:ℝ)≤(AffineSourceLibrary.domain (14:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window078.window.upper≤(AffineSourceLibrary.domain (14:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (14:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window078.valid.qb_lt_one.le
    Tilt00.retention_bound Decay00.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window078.window.activity_bounds Stage170SourceData.Window078.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window078.window.density Stage170SourceData.Window078.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell242Term01

end ForestUnimodality.SharedAffineData.EarlyStop20260928
