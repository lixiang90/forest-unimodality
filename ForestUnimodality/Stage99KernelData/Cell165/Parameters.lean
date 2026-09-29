import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 52
  A := (-10780704241658036102080587/10000000000000000000000000)
  B := (2574317175852715577910601/20000000000000000000000000)
  C := (26020316785979976563839/97656250000000000000000)
  dδ := (37012682512496661302314749/500000000000000000000000000)
  dM := (497262271980761206245647/250000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(11898370477907251885341111/2500000000000000000000000), (16430813627932053577751503/1000000000000000000000000)]
  retention := ![(3/5), (1/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (13/23)
  hi := (21/37)
  vmin := (336/1369)
  damping := (336/1369)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell165
