import ForestUnimodality.SharedAffineData.Screen20260928.Common
import ForestUnimodality.Stage170SourceData.Windows.Batch040_059
import ForestUnimodality.Stage170SourceData.Windows.Batch060_079

namespace ForestUnimodality.SharedAffineData.Screen20260928
open SharedAffineLaplace
set_option maxRecDepth 100000
set_option maxHeartbeats 0
variable {V : Type*} [DecidableEq V]

namespace Stage130Cell211Term00
def rate : ℚ := (131793763650136758341934373747/1000000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (10:Fin 15)).A (AffineSourceLibrary.parameters (10:Fin 15)).C Stage170SourceData.Window047.window.rho Tilt00.u Stage170SourceData.Window047.window.qa rate Decay00.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (10:Fin 15)).A (AffineSourceLibrary.parameters (10:Fin 15)).C Stage170SourceData.Window047.window.rho Tilt00.u Stage170SourceData.Window047.window.qb rate Decay00.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window047.window.qa:ℝ) (Stage170SourceData.Window047.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window047.window.upper:ℝ)≤(AffineSourceLibrary.domain (10:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window047.window.upper≤(AffineSourceLibrary.domain (10:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (10:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window047.valid.qb_lt_one.le
    Tilt00.retention_bound Decay00.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window047.window.activity_bounds Stage170SourceData.Window047.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window047.window.density Stage170SourceData.Window047.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell211Term00

namespace Stage130Cell211Term01
def rate : ℚ := (160157570497503816223401640939/1000000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (10:Fin 15)).A (AffineSourceLibrary.parameters (10:Fin 15)).C Stage170SourceData.Window047.window.rho Tilt01.u Stage170SourceData.Window047.window.qa rate Decay01.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (10:Fin 15)).A (AffineSourceLibrary.parameters (10:Fin 15)).C Stage170SourceData.Window047.window.rho Tilt01.u Stage170SourceData.Window047.window.qb rate Decay01.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window047.window.qa:ℝ) (Stage170SourceData.Window047.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt01.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window047.window.upper:ℝ)≤(AffineSourceLibrary.domain (10:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window047.window.upper≤(AffineSourceLibrary.domain (10:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (10:Fin 15)
    Tilt01.admissible.1 Tilt01.admissible.2 Stage170SourceData.Window047.valid.qb_lt_one.le
    Tilt01.retention_bound Decay01.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window047.window.activity_bounds Stage170SourceData.Window047.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window047.window.density Stage170SourceData.Window047.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell211Term01

namespace Stage130Cell212Term00
def rate : ℚ := (65889544154015115401750312053/500000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (11:Fin 15)).A (AffineSourceLibrary.parameters (11:Fin 15)).C Stage170SourceData.Window048.window.rho Tilt00.u Stage170SourceData.Window048.window.qa rate Decay02.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (11:Fin 15)).A (AffineSourceLibrary.parameters (11:Fin 15)).C Stage170SourceData.Window048.window.rho Tilt00.u Stage170SourceData.Window048.window.qb rate Decay02.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window048.window.qa:ℝ) (Stage170SourceData.Window048.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window048.window.upper:ℝ)≤(AffineSourceLibrary.domain (11:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window048.window.upper≤(AffineSourceLibrary.domain (11:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (11:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window048.valid.qb_lt_one.le
    Tilt00.retention_bound Decay02.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window048.window.activity_bounds Stage170SourceData.Window048.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window048.window.density Stage170SourceData.Window048.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell212Term00

namespace Stage130Cell213Term00
def rate : ℚ := (66428556764429861916658028449/500000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (11:Fin 15)).A (AffineSourceLibrary.parameters (11:Fin 15)).C Stage170SourceData.Window049.window.rho Tilt00.u Stage170SourceData.Window049.window.qa rate Decay02.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (11:Fin 15)).A (AffineSourceLibrary.parameters (11:Fin 15)).C Stage170SourceData.Window049.window.rho Tilt00.u Stage170SourceData.Window049.window.qb rate Decay02.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window049.window.qa:ℝ) (Stage170SourceData.Window049.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window049.window.upper:ℝ)≤(AffineSourceLibrary.domain (11:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window049.window.upper≤(AffineSourceLibrary.domain (11:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (11:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window049.valid.qb_lt_one.le
    Tilt00.retention_bound Decay02.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window049.window.activity_bounds Stage170SourceData.Window049.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window049.window.density Stage170SourceData.Window049.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell213Term00

namespace Stage130Cell214Term00
def rate : ℚ := (130736391013361064461189640929/1000000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (12:Fin 15)).A (AffineSourceLibrary.parameters (12:Fin 15)).C Stage170SourceData.Window050.window.rho Tilt00.u Stage170SourceData.Window050.window.qa rate Decay03.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (12:Fin 15)).A (AffineSourceLibrary.parameters (12:Fin 15)).C Stage170SourceData.Window050.window.rho Tilt00.u Stage170SourceData.Window050.window.qb rate Decay03.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window050.window.qa:ℝ) (Stage170SourceData.Window050.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window050.window.upper:ℝ)≤(AffineSourceLibrary.domain (12:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window050.window.upper≤(AffineSourceLibrary.domain (12:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (12:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window050.valid.qb_lt_one.le
    Tilt00.retention_bound Decay03.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window050.window.activity_bounds Stage170SourceData.Window050.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window050.window.density Stage170SourceData.Window050.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell214Term00

namespace Stage130Cell215Term00
def rate : ℚ := (65690682614915309945069402569/500000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (12:Fin 15)).A (AffineSourceLibrary.parameters (12:Fin 15)).C Stage170SourceData.Window051.window.rho Tilt00.u Stage170SourceData.Window051.window.qa rate Decay03.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (12:Fin 15)).A (AffineSourceLibrary.parameters (12:Fin 15)).C Stage170SourceData.Window051.window.rho Tilt00.u Stage170SourceData.Window051.window.qb rate Decay03.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window051.window.qa:ℝ) (Stage170SourceData.Window051.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window051.window.upper:ℝ)≤(AffineSourceLibrary.domain (12:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window051.window.upper≤(AffineSourceLibrary.domain (12:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (12:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window051.valid.qb_lt_one.le
    Tilt00.retention_bound Decay03.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window051.window.activity_bounds Stage170SourceData.Window051.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window051.window.density Stage170SourceData.Window051.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell215Term00

namespace Stage130Cell216Term00
def rate : ℚ := (132019235993881048986072132919/1000000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (12:Fin 15)).A (AffineSourceLibrary.parameters (12:Fin 15)).C Stage170SourceData.Window052.window.rho Tilt00.u Stage170SourceData.Window052.window.qa rate Decay03.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (12:Fin 15)).A (AffineSourceLibrary.parameters (12:Fin 15)).C Stage170SourceData.Window052.window.rho Tilt00.u Stage170SourceData.Window052.window.qb rate Decay03.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window052.window.qa:ℝ) (Stage170SourceData.Window052.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window052.window.upper:ℝ)≤(AffineSourceLibrary.domain (12:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window052.window.upper≤(AffineSourceLibrary.domain (12:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (12:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window052.valid.qb_lt_one.le
    Tilt00.retention_bound Decay03.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window052.window.activity_bounds Stage170SourceData.Window052.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window052.window.density Stage170SourceData.Window052.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell216Term00

namespace Stage130Cell217Term00
def rate : ℚ := (26530023799552005060668369667/200000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (12:Fin 15)).A (AffineSourceLibrary.parameters (12:Fin 15)).C Stage170SourceData.Window053.window.rho Tilt00.u Stage170SourceData.Window053.window.qa rate Decay03.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (12:Fin 15)).A (AffineSourceLibrary.parameters (12:Fin 15)).C Stage170SourceData.Window053.window.rho Tilt00.u Stage170SourceData.Window053.window.qb rate Decay03.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window053.window.qa:ℝ) (Stage170SourceData.Window053.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window053.window.upper:ℝ)≤(AffineSourceLibrary.domain (12:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window053.window.upper≤(AffineSourceLibrary.domain (12:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (12:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window053.valid.qb_lt_one.le
    Tilt00.retention_bound Decay03.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window053.window.activity_bounds Stage170SourceData.Window053.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window053.window.density Stage170SourceData.Window053.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell217Term00

namespace Stage130Cell218Term00
def rate : ℚ := (66637063734508374377011741311/500000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (12:Fin 15)).A (AffineSourceLibrary.parameters (12:Fin 15)).C Stage170SourceData.Window054.window.rho Tilt00.u Stage170SourceData.Window054.window.qa rate Decay03.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (12:Fin 15)).A (AffineSourceLibrary.parameters (12:Fin 15)).C Stage170SourceData.Window054.window.rho Tilt00.u Stage170SourceData.Window054.window.qb rate Decay03.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window054.window.qa:ℝ) (Stage170SourceData.Window054.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window054.window.upper:ℝ)≤(AffineSourceLibrary.domain (12:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window054.window.upper≤(AffineSourceLibrary.domain (12:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (12:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window054.valid.qb_lt_one.le
    Tilt00.retention_bound Decay03.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window054.window.activity_bounds Stage170SourceData.Window054.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window054.window.density Stage170SourceData.Window054.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell218Term00

namespace Stage130Cell219Term00
def rate : ℚ := (134488613001260786216369100859/1000000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (12:Fin 15)).A (AffineSourceLibrary.parameters (12:Fin 15)).C Stage170SourceData.Window055.window.rho Tilt00.u Stage170SourceData.Window055.window.qa rate Decay03.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (12:Fin 15)).A (AffineSourceLibrary.parameters (12:Fin 15)).C Stage170SourceData.Window055.window.rho Tilt00.u Stage170SourceData.Window055.window.qb rate Decay03.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window055.window.qa:ℝ) (Stage170SourceData.Window055.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window055.window.upper:ℝ)≤(AffineSourceLibrary.domain (12:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window055.window.upper≤(AffineSourceLibrary.domain (12:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (12:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window055.valid.qb_lt_one.le
    Tilt00.retention_bound Decay03.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window055.window.activity_bounds Stage170SourceData.Window055.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window055.window.density Stage170SourceData.Window055.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell219Term00

namespace Stage130Cell220Term00
def rate : ℚ := (16087301896897451019379552263/125000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window056.window.rho Tilt00.u Stage170SourceData.Window056.window.qa rate Decay04.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window056.window.rho Tilt00.u Stage170SourceData.Window056.window.qb rate Decay04.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window056.window.qa:ℝ) (Stage170SourceData.Window056.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window056.window.upper:ℝ)≤(AffineSourceLibrary.domain (13:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window056.window.upper≤(AffineSourceLibrary.domain (13:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (13:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window056.valid.qb_lt_one.le
    Tilt00.retention_bound Decay04.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window056.window.activity_bounds Stage170SourceData.Window056.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window056.window.density Stage170SourceData.Window056.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell220Term00

namespace Stage130Cell221Term00
def rate : ℚ := (64632793674250195035478535161/500000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window057.window.rho Tilt00.u Stage170SourceData.Window057.window.qa rate Decay04.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window057.window.rho Tilt00.u Stage170SourceData.Window057.window.qb rate Decay04.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window057.window.qa:ℝ) (Stage170SourceData.Window057.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window057.window.upper:ℝ)≤(AffineSourceLibrary.domain (13:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window057.window.upper≤(AffineSourceLibrary.domain (13:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (13:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window057.valid.qb_lt_one.le
    Tilt00.retention_bound Decay04.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window057.window.activity_bounds Stage170SourceData.Window057.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window057.window.density Stage170SourceData.Window057.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell221Term00

namespace Stage130Cell222Term00
def rate : ℚ := (129826796295382216493053551641/1000000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window058.window.rho Tilt00.u Stage170SourceData.Window058.window.qa rate Decay04.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window058.window.rho Tilt00.u Stage170SourceData.Window058.window.qb rate Decay04.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window058.window.qa:ℝ) (Stage170SourceData.Window058.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window058.window.upper:ℝ)≤(AffineSourceLibrary.domain (13:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window058.window.upper≤(AffineSourceLibrary.domain (13:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (13:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window058.valid.qb_lt_one.le
    Tilt00.retention_bound Decay04.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window058.window.activity_bounds Stage170SourceData.Window058.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window058.window.density Stage170SourceData.Window058.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell222Term00

namespace Stage130Cell223Term00
def rate : ℚ := (65191067355923295698463311817/500000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window059.window.rho Tilt00.u Stage170SourceData.Window059.window.qa rate Decay04.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window059.window.rho Tilt00.u Stage170SourceData.Window059.window.qb rate Decay04.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window059.window.qa:ℝ) (Stage170SourceData.Window059.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window059.window.upper:ℝ)≤(AffineSourceLibrary.domain (13:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window059.window.upper≤(AffineSourceLibrary.domain (13:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (13:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window059.valid.qb_lt_one.le
    Tilt00.retention_bound Decay04.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window059.window.activity_bounds Stage170SourceData.Window059.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window059.window.density Stage170SourceData.Window059.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell223Term00

namespace Stage130Cell224Term00
def rate : ℚ := (130931693409503439018902520557/1000000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window060.window.rho Tilt00.u Stage170SourceData.Window060.window.qa rate Decay04.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window060.window.rho Tilt00.u Stage170SourceData.Window060.window.qb rate Decay04.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window060.window.qa:ℝ) (Stage170SourceData.Window060.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window060.window.upper:ℝ)≤(AffineSourceLibrary.domain (13:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window060.window.upper≤(AffineSourceLibrary.domain (13:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (13:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window060.valid.qb_lt_one.le
    Tilt00.retention_bound Decay04.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window060.window.activity_bounds Stage170SourceData.Window060.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window060.window.density Stage170SourceData.Window060.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell224Term00

namespace Stage130Cell225Term00
def rate : ℚ := (132002551028409673307466741447/1000000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window061.window.rho Tilt00.u Stage170SourceData.Window061.window.qa rate Decay04.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window061.window.rho Tilt00.u Stage170SourceData.Window061.window.qb rate Decay04.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window061.window.qa:ℝ) (Stage170SourceData.Window061.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window061.window.upper:ℝ)≤(AffineSourceLibrary.domain (13:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window061.window.upper≤(AffineSourceLibrary.domain (13:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (13:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window061.valid.qb_lt_one.le
    Tilt00.retention_bound Decay04.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window061.window.activity_bounds Stage170SourceData.Window061.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window061.window.density Stage170SourceData.Window061.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell225Term00

namespace Stage130Cell226Term00
def rate : ℚ := (66536941930649242518442089047/500000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window062.window.rho Tilt00.u Stage170SourceData.Window062.window.qa rate Decay04.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window062.window.rho Tilt00.u Stage170SourceData.Window062.window.qb rate Decay04.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window062.window.qa:ℝ) (Stage170SourceData.Window062.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window062.window.upper:ℝ)≤(AffineSourceLibrary.domain (13:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window062.window.upper≤(AffineSourceLibrary.domain (13:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (13:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window062.valid.qb_lt_one.le
    Tilt00.retention_bound Decay04.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window062.window.activity_bounds Stage170SourceData.Window062.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window062.window.density Stage170SourceData.Window062.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell226Term00

namespace Stage130Cell227Term00
def rate : ℚ := (33604320946787507433843966751/250000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window063.window.rho Tilt00.u Stage170SourceData.Window063.window.qa rate Decay04.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window063.window.rho Tilt00.u Stage170SourceData.Window063.window.qb rate Decay04.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window063.window.qa:ℝ) (Stage170SourceData.Window063.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window063.window.upper:ℝ)≤(AffineSourceLibrary.domain (13:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window063.window.upper≤(AffineSourceLibrary.domain (13:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (13:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window063.valid.qb_lt_one.le
    Tilt00.retention_bound Decay04.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window063.window.activity_bounds Stage170SourceData.Window063.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window063.window.density Stage170SourceData.Window063.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell227Term00

namespace Stage130Cell228Term00
def rate : ℚ := (2121272051501389985237089759/15625000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window064.window.rho Tilt00.u Stage170SourceData.Window064.window.qa rate Decay04.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (13:Fin 15)).A (AffineSourceLibrary.parameters (13:Fin 15)).C Stage170SourceData.Window064.window.rho Tilt00.u Stage170SourceData.Window064.window.qb rate Decay04.hi := by decide +kernel
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (Stage170SourceData.Window064.window.qa:ℝ) (Stage170SourceData.Window064.window.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z Tilt00.retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hb : (Stage170SourceData.Window064.window.upper:ℝ)≤(AffineSourceLibrary.domain (13:Fin 15)).b := by
    exact_mod_cast (show Stage170SourceData.Window064.window.upper≤(AffineSourceLibrary.domain (13:Fin 15)).b from by decide +kernel)
  exact SharedAffineLaplace.actual_laplace (13:Fin 15)
    Tilt00.admissible.1 Tilt00.admissible.2 Stage170SourceData.Window064.valid.qb_lt_one.le
    Tilt00.retention_bound Decay04.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window064.window.activity_bounds Stage170SourceData.Window064.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window064.window.density Stage170SourceData.Window064.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell228Term00

namespace Stage130Cell237Term00
def rate : ℚ := (58388493209979575014980350259/500000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window073.window.rho Tilt00.u Stage170SourceData.Window073.window.qa rate Decay05.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window073.window.rho Tilt00.u Stage170SourceData.Window073.window.qb rate Decay05.hi := by decide +kernel
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
    Tilt00.retention_bound Decay05.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window073.window.activity_bounds Stage170SourceData.Window073.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window073.window.density Stage170SourceData.Window073.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell237Term00

namespace Stage130Cell238Term00
def rate : ℚ := (118379618915763648402513570053/1000000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window074.window.rho Tilt00.u Stage170SourceData.Window074.window.qa rate Decay05.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window074.window.rho Tilt00.u Stage170SourceData.Window074.window.qb rate Decay05.hi := by decide +kernel
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
    Tilt00.retention_bound Decay05.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window074.window.activity_bounds Stage170SourceData.Window074.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window074.window.density Stage170SourceData.Window074.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell238Term00

namespace Stage130Cell241Term00
def rate : ℚ := (122580773559509200964086928243/1000000000000000000000000000000)
theorem endpoints_checked : EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window077.window.rho Tilt00.u Stage170SourceData.Window077.window.qa rate Decay05.hi ∧
    EndpointAccepts (AffineSourceLibrary.parameters (14:Fin 15)).A (AffineSourceLibrary.parameters (14:Fin 15)).C Stage170SourceData.Window077.window.rho Tilt00.u Stage170SourceData.Window077.window.qb rate Decay05.hi := by decide +kernel
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
    Tilt00.retention_bound Decay05.decay_bound
    endpoints_checked.1 endpoints_checked.2 hB hG hz
    ((Stage170SourceData.Window077.window.activity_bounds Stage170SourceData.Window077.valid hz hq).2.trans hb) hS hq
    (Stage170SourceData.Window077.window.density Stage170SourceData.Window077.valid G hG S hz hq hrank)
#print axioms endpoints_checked
#print axioms actual_laplace
end Stage130Cell241Term00

end ForestUnimodality.SharedAffineData.Screen20260928
