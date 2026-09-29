import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell118
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (56458849624431326278127443343 / 200000000000000000000000000000)
  probabilityCap := (5381 / 10506)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 22), (76, 22), (77, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (3579 / 3425)
def activityUpper : ℚ := (5381 / 5125)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (27)
  A := (1085415792455697817587179 / 500000000000000000000000)
  B := (-2079433478920642702769683 / 100000000000000000000000000)
  C := (133563730367295199763511 / 1562500000000000000000000)
  dδ := (1344295271699467164694397 / 10000000000000000000000000)
  dM := (76679334118916242149901 / 78125000000000000000000000)
  wL := (908144678043 / 500000000000)
  wR := (682409576223 / 312500000000)
  wC := (1 / 10000000000000)
  price := ![(5548640022441907682093643 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (7885682585843272196513 / 312500000000000000000) else if j = 0 then (2672080561309546808956839 / 100000000000000000000000) else if j = 1 then (3773234143721029454354721 / 100000000000000000000000) else if j = 2 then (2059809352458377773587017 / 50000000000000000000000) else if j = 3 then (408540697621866755184783 / 25000000000000000000000) else if j = 4 then (17423586909150422741277 / 1000000000000000000000) else if j = 5 then (954648939861045064958489 / 50000000000000000000000) else if j = 6 then (113921761364160669671719 / 5000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (13600679723782205875114423 / 500000000000000000000000000000) else if j = 0 then (46393212535331713128806327 / 1000000000000000000000000000000) else if j = 1 then (81425079657438347121728243 / 1000000000000000000000000000000) else if j = 2 then (127026282894781325324915351 / 1000000000000000000000000000000) else if j = 3 then (39319485680472058166569807 / 250000000000000000000000000000) else if j = 4 then (39319485680472058166569807 / 250000000000000000000000000000) else if j = 5 then (39319485680472058166569807 / 250000000000000000000000000000) else if j = 6 then (39319485680472058166569807 / 250000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (3579 / 7004)
  hi := (5381 / 10506)
  vmin := (27577625 / 110376036)
  damping := (27577625 / 110376036)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell118
