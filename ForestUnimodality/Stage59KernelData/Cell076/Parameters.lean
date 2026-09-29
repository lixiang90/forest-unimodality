import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell076
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 18
  density := (17251153016544075690277703103 / 62500000000000000000000000000)
  probabilityCap := (49 / 99)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (60, 17), (60, 18), (61, 17), (61, 18), (62, 18), (63, 18), (64, 18), (65, 18)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (3193 / 3275)
def activityUpper : ℚ := (49 / 50)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (24)
  A := (1489727349587489494354031 / 500000000000000000000000)
  B := (-875907523155337354447969 / 12500000000000000000000000)
  C := (-278662541289249644782533 / 10000000000000000000000000)
  dδ := (336800377915408635787209 / 2500000000000000000000000)
  dM := (3348320749720719757998311 / 10000000000000000000000000000)
  wL := (302754734719 / 156250000000)
  wR := (2264561427963 / 1250000000000)
  wC := (62680138857 / 1000000000000)
  price := ![(3083602406742841139930533 / 500000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (1011256135033727865391029 / 50000000000000000000000) else if j = 0 then (1563169286657548440189203 / 100000000000000000000000) else if j = 1 then (2117068716032693487250071 / 100000000000000000000000) else if j = 2 then (1062153904892818978566993 / 50000000000000000000000) else if j = 3 then (1269517761924379684046471 / 100000000000000000000000) else if j = 4 then (1764965121377247925238407 / 100000000000000000000000) else if j = 5 then (1742652660745541126630087 / 100000000000000000000000) else if j = 6 then (833745010019248766752753 / 50000000000000000000000) else if j = 7 then (969564013236998611944273 / 50000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (807404209768817755918701 / 31250000000000000000000000000) else if j = 0 then (1892871842070167797390521 / 40000000000000000000000000000) else if j = 1 then (43266858166241311086588127 / 500000000000000000000000000000) else if j = 2 then (5675128138729350665203631 / 40000000000000000000000000000) else if j = 3 then (94102890055461171744447963 / 500000000000000000000000000000) else if j = 4 then (199433126491165748594983909 / 1000000000000000000000000000000) else if j = 5 then (199433126491165748594983909 / 1000000000000000000000000000000) else if j = 6 then (171470280713303884373994101 / 1000000000000000000000000000000) else if j = 7 then (30203098522144148729627241 / 250000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (3193 / 6468)
  hi := (49 / 99)
  vmin := (10457075 / 41835024)
  damping := (10457075 / 41835024)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell076
