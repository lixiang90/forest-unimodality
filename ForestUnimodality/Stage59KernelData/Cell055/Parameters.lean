import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell055
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 21
  density := (17042459192956493318899060431 / 62500000000000000000000000000)
  probabilityCap := (9237 / 19012)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (61, 17), (61, 18), (61, 19), (61, 20), (61, 21), (62, 17), (62, 18), (62, 19), (62, 20), (62, 21), (63, 18), (63, 19), (63, 20), (63, 21), (64, 18), (64, 19), (64, 20), (64, 21), (65, 18), (65, 19), (65, 20), (65, 21), (66, 18), (66, 19), (66, 20), (66, 21), (67, 19), (67, 20), (67, 21), (68, 19), (68, 20), (68, 21), (69, 19), (69, 20), (69, 21), (70, 20), (70, 21), (71, 20), (71, 21), (72, 20), (72, 21), (73, 20), (73, 21), (74, 21), (75, 21), (76, 21), (77, 21)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (47 / 50)
def activityUpper : ℚ := (9237 / 9775)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (31)
  A := (1467762426544681878482379 / 500000000000000000000000)
  B := (-676287236807130293092527 / 10000000000000000000000000)
  C := (-519117827408949669698579 / 5000000000000000000000000)
  dδ := (639144970281167457137883 / 5000000000000000000000000)
  dM := (0)
  wL := (2771346872601 / 1250000000000)
  wR := (4457306254797 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(803427227061979110089851 / 125000000000000000000000), (175583690391894053917099 / 100000000000000000000000)]
  retention := ![(4 / 5), (3 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (1160913222305153702507141 / 50000000000000000000000) else if j = 0 then (7652777211427861381309867 / 1000000000000000000000000) else if j = 1 then (558257406538505307480591 / 20000000000000000000000) else if j = 2 then (1110954545528137238363797 / 50000000000000000000000) else if j = 3 then (337405623809069421525919 / 25000000000000000000000) else if j = 4 then (469301991542980978522337 / 25000000000000000000000) else if j = 5 then (960650697784988949479157 / 50000000000000000000000) else if j = 6 then (2934109468666988629337311 / 500000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (25666051395182954520792799 / 1000000000000000000000000000000) else if j = 0 then (9832659758429078715248203 / 200000000000000000000000000000) else if j = 1 then (18137019023613237663895241 / 200000000000000000000000000000) else if j = 2 then (74732312312831678998169823 / 500000000000000000000000000000) else if j = 3 then (204447889031065076235158409 / 1000000000000000000000000000000) else if j = 4 then (224677130905488171506583819 / 1000000000000000000000000000000) else if j = 5 then (224677130905488171506583819 / 1000000000000000000000000000000) else if j = 6 then (224677130905488171506583819 / 1000000000000000000000000000000) else 0

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
end ForestUnimodality.Stage59KernelData.Cell055
