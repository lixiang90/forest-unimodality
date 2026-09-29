import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell102
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 19
  density := (279220410815494811999635067933 / 1000000000000000000000000000000)
  probabilityCap := (407 / 808)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (60, 17), (60, 18), (60, 19), (61, 18), (61, 19), (62, 18), (62, 19), (63, 18), (63, 19), (64, 18), (64, 19), (65, 19), (66, 19), (67, 19), (68, 19)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (203 / 201)
def activityUpper : ℚ := (407 / 401)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (24)
  A := (-1458958243684396498650813 / 1000000000000000000000000)
  B := (208168094529384867241717 / 1000000000000000000000000)
  C := (9205826489000415446817271 / 100000000000000000000000000)
  dδ := (1241976079274171862465437 / 10000000000000000000000000)
  dM := (2551550608224206328350503 / 500000000000000000000000000)
  wL := (0)
  wR := (834996558877 / 2500000000000)
  wC := (9165003441123 / 10000000000000)
  price := ![(384668655796943648184083 / 625000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (592336681828512201519743 / 25000000000000000000000) else if j = 0 then (2912044105795591519836307 / 100000000000000000000000) else if j = 1 then (4473794902268716100479651 / 100000000000000000000000) else if j = 2 then (3138243160396972442072183 / 50000000000000000000000) else if j = 3 then (764273977203469456753737 / 50000000000000000000000) else if j = 4 then (1903519980715617876398937 / 100000000000000000000000) else if j = 5 then (2003704340210569512237271 / 100000000000000000000000) else if j = 6 then (1334675086128535070884027 / 50000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (26274682670896360713098329 / 1000000000000000000000000000000) else if j = 0 then (11589385555779597809292721 / 250000000000000000000000000000) else if j = 1 then (84167268613821006915011011 / 1000000000000000000000000000000) else if j = 2 then (134546134638844795284003983 / 1000000000000000000000000000000) else if j = 3 then (172331449600073198480469967 / 1000000000000000000000000000000) else if j = 4 then (176321357476846769981860549 / 1000000000000000000000000000000) else if j = 5 then (176321357476846769981860549 / 1000000000000000000000000000000) else if j = 6 then (176321357476846769981860549 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (203 / 404)
  hi := (407 / 808)
  vmin := (163207 / 652864)
  damping := (163207 / 652864)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell102
