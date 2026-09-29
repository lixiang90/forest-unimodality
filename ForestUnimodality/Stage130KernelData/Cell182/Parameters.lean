import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell182
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-15848270727186388084817281/10000000000000000000000000)
  B := (5530427870248855876100791/50000000000000000000000000)
  C := (48871106130260024216771519/10000000000000000000000000000)
  dδ := (17620830544595785654982123/250000000000000000000000000)
  dM := (13253628791281835130888567/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(75354948233462071272015237/10000000000000000000000000), (11086589311743999530790461/2000000000000000000000000), (61270797236497799076460069/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95699/180624)
  hi := (7977/15052)
  vmin := (56437275/226562704)
  damping := (56437275/226562704)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell182
