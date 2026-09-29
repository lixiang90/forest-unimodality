import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell060
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 19
  density := (273644310281882930594772493241 / 1000000000000000000000000000000)
  probabilityCap := (9287 / 19012)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (60, 17), (60, 18), (60, 19), (61, 17), (61, 18), (61, 19), (62, 17), (62, 18), (62, 19), (63, 18), (63, 19), (64, 18), (64, 19), (65, 18), (65, 19), (66, 19), (67, 19), (68, 19), (69, 19)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (4631 / 4875)
def activityUpper : ℚ := (9287 / 9725)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (25)
  A := (496923150436608490809931 / 200000000000000000000000)
  B := (-4179767171756400279125643 / 100000000000000000000000000)
  C := (-321418784605852561608863 / 6250000000000000000000000)
  dδ := (639739971890059128112327 / 5000000000000000000000000)
  dM := (6534056600745236000754579 / 10000000000000000000000000000)
  wL := (266215182499 / 125000000000)
  wR := (4675696350019 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(5539304053742922562264539 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (1042367615479217235474607 / 50000000000000000000000) else if j = 0 then (322105869358229455201581 / 20000000000000000000000) else if j = 1 then (1138707362450113080853953 / 50000000000000000000000) else if j = 2 then (1911674257255694797663637 / 100000000000000000000000) else if j = 3 then (331266795918075329652197 / 25000000000000000000000) else if j = 4 then (1966406047559336656149753 / 100000000000000000000000) else if j = 5 then (2397897921163845680325721 / 100000000000000000000000) else if j = 6 then (804490294250123696429 / 40000000000000000000) else if j = 7 then (150428769271522533301777 / 6250000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (1621610118879498063664607 / 62500000000000000000000000000) else if j = 0 then (6147333001971464551213789 / 125000000000000000000000000000) else if j = 1 then (17952707757744379548772549 / 200000000000000000000000000000) else if j = 2 then (29447047320550135515238877 / 200000000000000000000000000000) else if j = 3 then (99929748391172377968049661 / 500000000000000000000000000000) else if j = 4 then (108667424620901372244745093 / 500000000000000000000000000000) else if j = 5 then (108667424620901372244745093 / 500000000000000000000000000000) else if j = 6 then (108667424620901372244745093 / 500000000000000000000000000000) else if j = 7 then (11985086942505527427613531 / 62500000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (4631 / 9506)
  hi := (9287 / 19012)
  vmin := (22576125 / 90364036)
  damping := (22576125 / 90364036)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell060
