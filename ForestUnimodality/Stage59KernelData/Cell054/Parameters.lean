import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell054
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 19
  density := (17042459192956493318899060431 / 62500000000000000000000000000)
  probabilityCap := (9237 / 19012)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (60, 17), (60, 18), (60, 19), (61, 17), (61, 18), (61, 19), (62, 17), (62, 18), (62, 19), (63, 18), (63, 19), (64, 18), (64, 19), (65, 18), (65, 19), (66, 18), (66, 19), (67, 19), (68, 19), (69, 19)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (47 / 50)
def activityUpper : ℚ := (9237 / 9775)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (25)
  A := (2044332841543604091128827 / 1000000000000000000000000)
  B := (-298782135034594137357189 / 20000000000000000000000000)
  C := (-6417407090790991364137597 / 100000000000000000000000000)
  dδ := (1266826134357323940804463 / 10000000000000000000000000)
  dM := (268090409977878702495191 / 250000000000000000000000000)
  wL := (5410045776073 / 2500000000000)
  wR := (2294977111963 / 1250000000000)
  wC := (1 / 10000000000000)
  price := ![(4900313230193241942345139 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (2074106992411388361574609 / 100000000000000000000000) else if j = 0 then (870930970807098780994693 / 50000000000000000000000) else if j = 1 then (1161896383642328522967091 / 50000000000000000000000) else if j = 2 then (485614730898939139791537 / 25000000000000000000000) else if j = 3 then (135025735279828733581553 / 10000000000000000000000) else if j = 4 then (2076820510617536186259713 / 100000000000000000000000) else if j = 5 then (1382190919612457591370003 / 50000000000000000000000) else if j = 6 then (61153068383730008861221 / 2000000000000000000000) else if j = 7 then (1307293476207280313872161 / 50000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (25666051395182954520792799 / 1000000000000000000000000000000) else if j = 0 then (9832659758429078715248203 / 200000000000000000000000000000) else if j = 1 then (18137019023613237663895241 / 200000000000000000000000000000) else if j = 2 then (74732312312831678998169823 / 500000000000000000000000000000) else if j = 3 then (204447889031065076235158409 / 1000000000000000000000000000000) else if j = 4 then (224677130905488171506583819 / 1000000000000000000000000000000) else if j = 5 then (224677130905488171506583819 / 1000000000000000000000000000000) else if j = 6 then (224677130905488171506583819 / 1000000000000000000000000000000) else if j = 7 then (100168768152991975589012973 / 500000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (47 / 97)
  hi := (9237 / 19012)
  vmin := (2350 / 9409)
  damping := (2350 / 9409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell054
