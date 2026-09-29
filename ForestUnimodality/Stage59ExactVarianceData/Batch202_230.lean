import ForestUnimodality.Stage80ExactConstantProfile
import ForestUnimodality.Stage80ConstantWindows

/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell202
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 113308987825975932841775990297/500000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 0).source * (window 0).qa -
      (window 0).qa * (1-(window 0).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 0).source * (window 0).qb -
      (window 0).qb * (1-(window 0).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (6/11 : ℝ) (97/177 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 0).qa:ℝ) ((window 0).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((6/11:ℚ):ℝ) ((97/177:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 0).exact_total_variance (checked 0) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell202


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell203
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 114532984774649665446282035097/500000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 1).source * (window 1).qa -
      (window 1).qa * (1-(window 1).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 1).source * (window 1).qb -
      (window 1).qb * (1-(window 1).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (97/177 : ℝ) (49/89 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 1).qa:ℝ) ((window 1).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((97/177:ℚ):ℝ) ((49/89:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 1).exact_total_variance (checked 1) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell203


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell204
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 44087567758809025935520114853/200000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 2).source * (window 2).qa -
      (window 2).qa * (1-(window 2).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 2).source * (window 2).qb -
      (window 2).qb * (1-(window 2).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (49/89 : ℝ) (99/179 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 2).qa:ℝ) ((window 2).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((49/89:ℚ):ℝ) ((99/179:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 2).exact_total_variance (checked 2) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell204


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell205
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 111403432098765432098765432099/500000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 3).source * (window 3).qa -
      (window 3).qa * (1-(window 3).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 3).source * (window 3).qb -
      (window 3).qb * (1-(window 3).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (99/179 : ℝ) (5/9 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 3).qa:ℝ) ((window 3).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((99/179:ℚ):ℝ) ((5/9:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 3).exact_total_variance (checked 3) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell205


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell206
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 119329612845107237041704590539/500000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 4).source * (window 4).qa -
      (window 4).qa * (1-(window 4).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 4).source * (window 4).qb -
      (window 4).qb * (1-(window 4).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (5/9 : ℝ) (116/207 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 4).qa:ℝ) ((window 4).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((5/9:ℚ):ℝ) ((116/207:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 4).exact_total_variance (checked 4) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell206


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell207
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 48689430321361058601134215501/200000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 5).source * (window 5).qa -
      (window 5).qa * (1-(window 5).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 5).source * (window 5).qb -
      (window 5).qb * (1-(window 5).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (116/207 : ℝ) (13/23 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 5).qa:ℝ) ((window 5).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((116/207:ℚ):ℝ) ((13/23:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 5).exact_total_variance (checked 5) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell207


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell208
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 62001714992695398100803506209/250000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 6).source * (window 6).qa -
      (window 6).qa * (1-(window 6).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 6).source * (window 6).qb -
      (window 6).qb * (1-(window 6).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (13/23 : ℝ) (21/37 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 6).qa:ℝ) ((window 6).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((13/23:ℚ):ℝ) ((21/37:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 6).exact_total_variance (checked 6) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell208


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell209
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 50069541452191004740432419933/200000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 7).source * (window 7).qa -
      (window 7).qa * (1-(window 7).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 7).source * (window 7).qb -
      (window 7).qb * (1-(window 7).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (21/37 : ℝ) (53/93 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 7).qa:ℝ) ((window 7).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((21/37:ℚ):ℝ) ((53/93:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 7).exact_total_variance (checked 7) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell209


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell210
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 50534831262546827189796677057/200000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 8).source * (window 8).qa -
      (window 8).qa * (1-(window 8).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 8).source * (window 8).qb -
      (window 8).qb * (1-(window 8).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (53/93 : ℝ) (107/187 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 8).qa:ℝ) ((window 8).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((53/93:ℚ):ℝ) ((107/187:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 8).exact_total_variance (checked 8) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell210


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell211
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 254986268039837030330466274333/1000000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 9).source * (window 9).qa -
      (window 9).qa * (1-(window 9).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 9).source * (window 9).qb -
      (window 9).qb * (1-(window 9).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (107/187 : ℝ) (27/47 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 9).qa:ℝ) ((window 9).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((107/187:ℚ):ℝ) ((27/47:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 9).exact_total_variance (checked 9) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell211


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell212
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 64879950979735677279814898647/250000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 10).source * (window 10).qa -
      (window 10).qa * (1-(window 10).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 10).source * (window 10).qb -
      (window 10).qb * (1-(window 10).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (27/47 : ℝ) (653/1128 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 10).qa:ℝ) ((window 10).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((27/47:ℚ):ℝ) ((653/1128:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 10).exact_total_variance (checked 10) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell212


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell213
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 33011579513888888888888888889/125000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 11).source * (window 11).qa -
      (window 11).qa * (1-(window 11).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 11).source * (window 11).qb -
      (window 11).qb * (1-(window 11).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (653/1128 : ℝ) (7/12 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 11).qa:ℝ) ((window 11).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((653/1128:ℚ):ℝ) ((7/12:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 11).exact_total_variance (checked 11) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell213


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell214
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 269879409012345679012345679013/1000000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 12).source * (window 12).qa -
      (window 12).qa * (1-(window 12).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 12).source * (window 12).qb -
      (window 12).qb * (1-(window 12).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (7/12 : ℝ) (53/90 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 12).qa:ℝ) ((window 12).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((7/12:ℚ):ℝ) ((53/90:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 12).exact_total_variance (checked 12) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell214


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell215
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 275727910308641975308641975309/1000000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 13).source * (window 13).qa -
      (window 13).qa * (1-(window 13).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 13).source * (window 13).qb -
      (window 13).qb * (1-(window 13).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (53/90 : ℝ) (107/180 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 13).qa:ℝ) ((window 13).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((53/90:ℚ):ℝ) ((107/180:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 13).exact_total_variance (checked 13) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell215


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell216
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 14081907/50000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 14).source * (window 14).qa -
      (window 14).qa * (1-(window 14).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 14).source * (window 14).qb -
      (window 14).qb * (1-(window 14).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (107/180 : ℝ) (3/5 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 14).qa:ℝ) ((window 14).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((107/180:ℚ):ℝ) ((3/5:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 14).exact_total_variance (checked 14) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell216


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell217
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 297323737419010410347254240579/1000000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 15).source * (window 15).qa -
      (window 15).qa * (1-(window 15).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 15).source * (window 15).qb -
      (window 15).qb * (1-(window 15).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (3/5 : ℝ) (123/203 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 15).qa:ℝ) ((window 15).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((3/5:ℚ):ℝ) ((123/203:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 15).exact_total_variance (checked 15) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell217


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell218
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 60730065402959751154679988689/200000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 16).source * (window 16).qa -
      (window 16).qa * (1-(window 16).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 16).source * (window 16).qb -
      (window 16).qb * (1-(window 16).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (123/203 : ℝ) (63/103 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 16).qa:ℝ) ((window 16).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((123/203:ℚ):ℝ) ((63/103:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 16).exact_total_variance (checked 16) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell218


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell219
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 77464589556672237357203360729/250000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 17).source * (window 17).qa -
      (window 17).qa * (1-(window 17).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 17).source * (window 17).qb -
      (window 17).qb * (1-(window 17).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (63/103 : ℝ) (129/209 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 17).qa:ℝ) ((window 17).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((63/103:ℚ):ℝ) ((129/209:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 17).exact_total_variance (checked 17) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell219


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell220
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 315950224741901032395870416519/1000000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 18).source * (window 18).qa -
      (window 18).qa * (1-(window 18).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 18).source * (window 18).qb -
      (window 18).qb * (1-(window 18).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (129/209 : ℝ) (33/53 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 18).qa:ℝ) ((window 18).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((129/209:ℚ):ℝ) ((33/53:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 18).exact_total_variance (checked 18) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell220


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell221
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 323610704953102636569045560553/1000000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 19).source * (window 19).qa -
      (window 19).qa * (1-(window 19).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 19).source * (window 19).qb -
      (window 19).qb * (1-(window 19).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (33/53 : ℝ) (467/742 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 19).qa:ℝ) ((window 19).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((33/53:ℚ):ℝ) ((467/742:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 19).exact_total_variance (checked 19) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell221


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell222
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 165681000563785499960040976163/500000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 20).source * (window 20).qa -
      (window 20).qa * (1-(window 20).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 20).source * (window 20).qb -
      (window 20).qb * (1-(window 20).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (467/742 : ℝ) (236/371 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 20).qa:ℝ) ((window 20).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((467/742:ℚ):ℝ) ((236/371:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 20).exact_total_variance (checked 20) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell222


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell223
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 339204113265306122448979591837/1000000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 21).source * (window 21).qa -
      (window 21).qa * (1-(window 21).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 21).source * (window 21).qb -
      (window 21).qb * (1-(window 21).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (236/371 : ℝ) (9/14 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 21).qa:ℝ) ((window 21).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((236/371:ℚ):ℝ) ((9/14:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 21).exact_total_variance (checked 21) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell223


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell224
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 45844349370118417737465356513/125000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 22).source * (window 22).qa -
      (window 22).qa * (1-(window 22).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 22).source * (window 22).qb -
      (window 22).qb * (1-(window 22).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (9/14 : ℝ) (41/63 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 22).qa:ℝ) ((window 22).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((9/14:ℚ):ℝ) ((41/63:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 22).exact_total_variance (checked 22) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell224


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell225
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 376455431544469639707734945831/1000000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 23).source * (window 23).qa -
      (window 23).qa * (1-(window 23).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 23).source * (window 23).qb -
      (window 23).qb * (1-(window 23).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (41/63 : ℝ) (83/126 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 23).qa:ℝ) ((window 23).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((41/63:ℚ):ℝ) ((83/126:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 23).exact_total_variance (checked 23) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell225


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell226
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 77256408888888888888888888889/200000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 24).source * (window 24).qa -
      (window 24).qa * (1-(window 24).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 24).source * (window 24).qb -
      (window 24).qb * (1-(window 24).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (83/126 : ℝ) (2/3 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 24).qa:ℝ) ((window 24).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((83/126:ℚ):ℝ) ((2/3:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 24).exact_total_variance (checked 24) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell226


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell227
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 49288861316568047337278106509/125000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 25).source * (window 25).qa -
      (window 25).qa * (1-(window 25).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 25).source * (window 25).qb -
      (window 25).qb * (1-(window 25).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (2/3 : ℝ) (35/52 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 25).qa:ℝ) ((window 25).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((2/3:ℚ):ℝ) ((35/52:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 25).exact_total_variance (checked 25) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell227


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell228
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 402421919395134779750164365549/1000000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 26).source * (window 26).qa -
      (window 26).qa * (1-(window 26).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 26).source * (window 26).qb -
      (window 26).qb * (1-(window 26).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (35/52 : ℝ) (53/78 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 26).qa:ℝ) ((window 26).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((35/52:ℚ):ℝ) ((53/78:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 26).exact_total_variance (checked 26) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell228


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell229
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 410615131032215647600262984879/1000000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 27).source * (window 27).qa -
      (window 27).qa * (1-(window 27).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 27).source * (window 27).qb -
      (window 27).qb * (1-(window 27).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (53/78 : ℝ) (107/156 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 27).qa:ℝ) ((window 27).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((53/78:ℚ):ℝ) ((107/156:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 27).exact_total_variance (checked 27) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell229


/-! Actual forest variance profile only; finite kernels, density, availability,
Laplace inputs and no-valley assembly remain separate obligations. -/
namespace ForestUnimodality.Stage59ExactVarianceData.Cell230
open Stage80ConstantWindows
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := 20944526272189349112426035503/50000000000000000000000000000

theorem endpoints_checked :
    Stage80ConstantLibrary.factor (window 28).source * (window 28).qa -
      (window 28).qa * (1-(window 28).qa) ≤ alpha ∧
    Stage80ConstantLibrary.factor (window 28).source * (window 28).qb -
      (window 28).qb * (1-(window 28).qb) ≤ alpha := by
  decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (107/156 : ℝ) (9/13 : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+0 := by
  have hqw : z/(1+z) ∈ Set.Icc ((window 28).qa:ℝ) ((window 28).qb:ℝ) := by
    change z/(1+z) ∈ Set.Icc ((107/156:ℚ):ℝ) ((9/13:ℚ):ℝ)
    norm_num
    exact hq
  exact (window 28).exact_total_variance (checked 28) alpha
    endpoints_checked.1 endpoints_checked.2 hB hG hz hqw

#print axioms endpoints_checked
#print axioms actual_variance
end ForestUnimodality.Stage59ExactVarianceData.Cell230
