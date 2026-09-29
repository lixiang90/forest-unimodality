import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell186
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 17
  A := (3696795896134218084760903/20000000000000000000000000)
  B := (26350127296695911860435757/1000000000000000000000000000)
  C := (49836294032578429269442211/1000000000000000000000000000)
  dδ := (30828264318178560943195521/1000000000000000000000000000)
  dM := (15882882850670783782091877/50000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(3011811903438372239882881/2500000000000000000000000), (43481784238011762511177949/10000000000000000000000000)]
  retention := ![(7/10), (3/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53/78)
  hi := (107/156)
  vmin := (5243/24336)
  damping := (13107500000000000000000000000000000000000000/150116682940569144593175659726526589679581089)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell186
