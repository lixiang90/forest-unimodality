import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell063
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 19
  density := (10965039727666275883725687439 / 40000000000000000000000000000)
  probabilityCap := (24 / 49)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (60, 17), (60, 18), (60, 19), (61, 17), (61, 18), (61, 19), (62, 17), (62, 18), (62, 19), (63, 18), (63, 19), (64, 18), (64, 19), (65, 18), (65, 19), (66, 19), (67, 19), (68, 19), (69, 19)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (9287 / 9725)
def activityUpper : ℚ := (24 / 25)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (25)
  A := (503732811636811500721933 / 200000000000000000000000)
  B := (-861778242965756946514233 / 20000000000000000000000000)
  C := (-5704499967217640382655119 / 100000000000000000000000000)
  dδ := (643955537757560786404909 / 5000000000000000000000000)
  dM := (6543302881998401369922913 / 10000000000000000000000000000)
  wL := (2668165756771 / 1250000000000)
  wR := (4663668486457 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(5622130689500462352725663 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (517008513994312490780203 / 25000000000000000000000) else if j = 0 then (759928348972533651561889 / 50000000000000000000000) else if j = 1 then (1142391610267096169195611 / 50000000000000000000000) else if j = 2 then (1925816211486719353729313 / 100000000000000000000000) else if j = 3 then (334684715112894259902987 / 25000000000000000000000) else if j = 4 then (994078053166679609375933 / 50000000000000000000000) else if j = 5 then (1204375880414227850678799 / 50000000000000000000000) else if j = 6 then (1939394624865622773768337 / 100000000000000000000000) else if j = 7 then (2431691415209087026028101 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (26080600837363311916222579 / 1000000000000000000000000000000) else if j = 0 then (24587393815680436115595113 / 500000000000000000000000000000) else if j = 1 then (44642688283538359299062491 / 500000000000000000000000000000) else if j = 2 then (29219999316944179249893621 / 200000000000000000000000000000) else if j = 3 then (19756025458748306783501109 / 100000000000000000000000000000) else if j = 4 then (213707006164344664725372573 / 1000000000000000000000000000000) else if j = 5 then (213707006164344664725372573 / 1000000000000000000000000000000) else if j = 6 then (213707006164344664725372573 / 1000000000000000000000000000000) else if j = 7 then (3751415424567007038967767 / 20000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (9287 / 19012)
  hi := (24 / 49)
  vmin := (90316075 / 361456144)
  damping := (90316075 / 361456144)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell063
