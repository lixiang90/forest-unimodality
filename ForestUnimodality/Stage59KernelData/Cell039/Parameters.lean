import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell039
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 16
  upperRank := 20
  density := (268674464704360484040076183601 / 1000000000000000000000000000000)
  probabilityCap := (1733 / 3648)

def pairs : List (ℕ × ℕ) := [(59, 16), (59, 17), (59, 18), (59, 19), (59, 20), (60, 17), (60, 18), (60, 19), (60, 20), (61, 17), (61, 18), (61, 19), (61, 20), (62, 17), (62, 18), (62, 19), (62, 20), (63, 17), (63, 18), (63, 19), (63, 20), (64, 18), (64, 19), (64, 20), (65, 18), (65, 19), (65, 20), (66, 18), (66, 19), (66, 20), (67, 19), (67, 20), (68, 19), (68, 20), (69, 19), (69, 20), (70, 19), (70, 20), (71, 20), (72, 20), (73, 20), (74, 20)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (9 / 10)
def activityUpper : ℚ := (1733 / 1915)

def row : RationalRow (Fin 0) where
  terms := Finset.univ
  scale := (27)
  A := (-2531857302880318931869397 / 1000000000000000000000000)
  B := (3150957566365314432843547 / 10000000000000000000000000)
  C := (-3349167508634408596535081 / 10000000000000000000000000)
  dδ := (50089220017806813586847 / 312500000000000000000000)
  dM := (3569883890515553048761177 / 500000000000000000000000000)
  wL := (1661455059689 / 625000000000)
  wR := (3354179761243 / 2500000000000)
  wC := (1 / 10000000000000)
  price := fun i => Fin.elim0 i
  retention := fun i => Fin.elim0 i
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (1670863884994425418994979 / 100000000000000000000000) else if j = 0 then (1461311912883589136935569 / 10000000000000000000000000) else if j = 1 then (3106993429215927804420971 / 100000000000000000000000) else if j = 2 then (623430594112366787129531 / 25000000000000000000000) else if j = 3 then (101161065673855318891583 / 4000000000000000000000) else if j = 4 then (137285957125457560579207 / 5000000000000000000000) else if j = 5 then (4087716555214063873791019 / 100000000000000000000000) else if j = 6 then (941594263968981834977967 / 20000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (41741094674072343480779981 / 1000000000000000000000000000000) else if j = 0 then (84598629642999239830841911 / 1000000000000000000000000000000) else if j = 1 then (155805323876075730213562473 / 1000000000000000000000000000000) else if j = 2 then (111909219212201537901518689 / 500000000000000000000000000000) else if j = 3 then (128418176114494218944427711 / 500000000000000000000000000000) else if j = 4 then (128418176114494218944427711 / 500000000000000000000000000000) else if j = 5 then (128418176114494218944427711 / 500000000000000000000000000000) else if j = 6 then (128418176114494218944427711 / 500000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (9 / 19)
  hi := (1733 / 3648)
  vmin := (90 / 361)
  damping := (90 / 361)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell039
