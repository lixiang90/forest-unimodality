import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell066
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 19
  density := (137303574933144262173784011173 / 500000000000000000000000000000)
  probabilityCap := (9529 / 19404)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (60, 17), (60, 18), (60, 19), (61, 17), (61, 18), (61, 19), (62, 18), (62, 19), (63, 18), (63, 19), (64, 18), (64, 19), (65, 18), (65, 19), (66, 19), (67, 19), (68, 19), (69, 19)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (24 / 25)
def activityUpper : ℚ := (9529 / 9875)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (25)
  A := (2723683407114519423487309 / 1000000000000000000000000)
  B := (-5522439105453030849801621 / 100000000000000000000000000)
  C := (-3225097367347526389202983 / 50000000000000000000000000)
  dδ := (653093632106742649767739 / 5000000000000000000000000)
  dM := (4697897378858524337214009 / 10000000000000000000000000000)
  wL := (669308034819 / 312500000000)
  wR := (4645535721447 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(5912283331729730306847159 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (2044699716083755802742417 / 100000000000000000000000) else if j = 0 then (724051535733470608136031 / 50000000000000000000000) else if j = 1 then (1145560724634742477689997 / 50000000000000000000000) else if j = 2 then (387285420909961501934049 / 20000000000000000000000) else if j = 3 then (672419096100210289534971 / 50000000000000000000000) else if j = 4 then (1998814488236276787347379 / 100000000000000000000000) else if j = 5 then (483068938143814037289303 / 20000000000000000000000) else if j = 6 then (481388802467241649907237 / 25000000000000000000000) else if j = 7 then (303889062669701015551027 / 12500000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (6343389563686620286395819 / 250000000000000000000000000000) else if j = 0 then (23598666551423093326961757 / 500000000000000000000000000000) else if j = 1 then (21820316176577447529169989 / 250000000000000000000000000000) else if j = 2 then (72360372670778396675597823 / 500000000000000000000000000000) else if j = 3 then (4874206549276512054376047 / 25000000000000000000000000000) else if j = 4 then (104909331126912181155340663 / 500000000000000000000000000000) else if j = 5 then (104909331126912181155340663 / 500000000000000000000000000000) else if j = 6 then (104909331126912181155340663 / 500000000000000000000000000000) else if j = 7 then (45802748181924893400806701 / 250000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (24 / 49)
  hi := (9529 / 19404)
  vmin := (600 / 2401)
  damping := (600 / 2401)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell066
