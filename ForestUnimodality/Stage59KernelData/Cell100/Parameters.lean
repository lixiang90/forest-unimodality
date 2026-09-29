import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell100
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (278772154011212467883159759871 / 1000000000000000000000000000000)
  probabilityCap := (203 / 404)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 18), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 19), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 20), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 21), (75, 22), (76, 22), (77, 22), (78, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (405 / 403)
def activityUpper : ℚ := (203 / 201)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (30)
  A := (-702568294656743028923529 / 2000000000000000000000000)
  B := (558167005859465312211931 / 5000000000000000000000000)
  C := (1766894401517069349005773 / 100000000000000000000000000)
  dδ := (311181967513028991112467 / 2500000000000000000000000)
  dM := (172091861541013744704709 / 62500000000000000000000000)
  wL := (73911150611 / 625000000000)
  wR := (222189161507 / 1250000000000)
  wC := (4629988537271 / 5000000000000)
  price := ![(1561764955449988612201651 / 1000000000000000000000000), (3788379146419854848204523 / 1000000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (614900812585699441115139 / 25000000000000000000000) else if j = 0 then (826783667898646257299333 / 50000000000000000000000) else if j = 1 then (593858731723636523724963 / 25000000000000000000000) else if j = 2 then (2011175320526561449696601 / 100000000000000000000000) else if j = 3 then (1341211283325341163674693 / 100000000000000000000000) else if j = 4 then (1429807999056336775822729 / 100000000000000000000000) else if j = 5 then (1668600484634910685599607 / 200000000000000000000000) else if j = 6 then (1216181541913326036308263 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (26116016463011584545536237 / 1000000000000000000000000000000) else if j = 0 then (46306282055269972784804567 / 1000000000000000000000000000000) else if j = 1 then (84491457148313223951554287 / 1000000000000000000000000000000) else if j = 2 then (27109728634825757717829793 / 200000000000000000000000000000) else if j = 3 then (174477145130048534277559727 / 1000000000000000000000000000000) else if j = 4 then (44850675758846788344274187 / 250000000000000000000000000000) else if j = 5 then (44850675758846788344274187 / 250000000000000000000000000000) else if j = 6 then (44850675758846788344274187 / 250000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (405 / 808)
  hi := (203 / 404)
  vmin := (40803 / 163216)
  damping := (40803 / 163216)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell100
