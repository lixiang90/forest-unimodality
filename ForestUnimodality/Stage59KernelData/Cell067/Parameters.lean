import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell067
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 21
  density := (137303574933144262173784011173 / 500000000000000000000000000000)
  probabilityCap := (9529 / 19404)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (61, 17), (61, 18), (61, 19), (61, 20), (61, 21), (62, 18), (62, 19), (62, 20), (62, 21), (63, 18), (63, 19), (63, 20), (63, 21), (64, 18), (64, 19), (64, 20), (64, 21), (65, 18), (65, 19), (65, 20), (65, 21), (66, 19), (66, 20), (66, 21), (67, 19), (67, 20), (67, 21), (68, 19), (68, 20), (68, 21), (69, 19), (69, 20), (69, 21), (70, 20), (70, 21), (71, 20), (71, 21), (72, 20), (72, 21), (73, 21), (74, 21), (75, 21), (76, 21)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (24 / 25)
def activityUpper : ℚ := (9529 / 9875)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (30)
  A := (144427166029444682732219 / 50000000000000000000000)
  B := (-3408902944349406077817477 / 50000000000000000000000000)
  C := (-5181063875329145612669279 / 100000000000000000000000000)
  dδ := (614846959766914974432339 / 5000000000000000000000000)
  dM := (0)
  wL := (529451224861 / 250000000000)
  wR := (4705487751389 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(1630763980040623728484661 / 250000000000000000000000), (1025540626314437077371 / 781250000000000000000)]
  retention := ![(4 / 5), (3 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (2379074632751794737828277 / 100000000000000000000000) else if j = 0 then (37069982237879073316833 / 3125000000000000000000) else if j = 1 then (2607863926043873803450879 / 100000000000000000000000) else if j = 2 then (2131439038344133862779017 / 100000000000000000000000) else if j = 3 then (1358889639886561795378839 / 100000000000000000000000) else if j = 4 then (174241494717115372736771 / 10000000000000000000000) else if j = 5 then (239359089891091549873181 / 20000000000000000000000) else if j = 6 then (1527733232875615598800323 / 200000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (6343389563686620286395819 / 250000000000000000000000000000) else if j = 0 then (23598666551423093326961757 / 500000000000000000000000000000) else if j = 1 then (21820316176577447529169989 / 250000000000000000000000000000) else if j = 2 then (72360372670778396675597823 / 500000000000000000000000000000) else if j = 3 then (4874206549276512054376047 / 25000000000000000000000000000) else if j = 4 then (104909331126912181155340663 / 500000000000000000000000000000) else if j = 5 then (104909331126912181155340663 / 500000000000000000000000000000) else if j = 6 then (104909331126912181155340663 / 500000000000000000000000000000) else 0

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
end ForestUnimodality.Stage59KernelData.Cell067
