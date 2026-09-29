import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell150
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (286273309301194164995767912653 / 1000000000000000000000000000000)
  probabilityCap := (2294 / 4389)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (4583 / 4195)
def activityUpper : ℚ := (2294 / 2095)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (2999702221610218406567583 / 1000000000000000000000000)
  B := (-1417260646955349062681151 / 25000000000000000000000000)
  C := (449001137659885141140137 / 2000000000000000000000000)
  dδ := (1511553254759780695604121 / 10000000000000000000000000)
  dM := (594483507786550363465039 / 1000000000000000000000000000)
  wL := (3864912124757 / 2500000000000)
  wR := (3067543937621 / 1250000000000)
  wC := (1 / 10000000000000)
  price := ![(7067110781998652946356287 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4}
  fixedPrice := fun j => if j = -1 then (260492598331935809596871 / 10000000000000000000000) else if j = 0 then (77881086248784192616057 / 3125000000000000000000) else if j = 1 then (200429989110542798869119 / 5000000000000000000000) else if j = 2 then (5879406001409824256143111 / 100000000000000000000000) else if j = 3 then (1822793415497537594660571 / 25000000000000000000000) else if j = 4 then (1846311354027266649069361 / 500000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (27262415507971706612097323 / 1000000000000000000000000000000) else if j = 0 then (5535599233164185869323367 / 125000000000000000000000000000) else if j = 1 then (37088948747449318320950513 / 500000000000000000000000000000) else if j = 2 then (112905183995795294801498583 / 1000000000000000000000000000000) else if j = 3 then (67022072496196269701805011 / 500000000000000000000000000000) else if j = 4 then (67022072496196269701805011 / 500000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (4583 / 8778)
  hi := (2294 / 4389)
  vmin := (4805930 / 19263321)
  damping := (4805930 / 19263321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell150
