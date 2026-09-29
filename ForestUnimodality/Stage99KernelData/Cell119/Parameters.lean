import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 60
  A := (-88164352110443415909912801/100000000000000000000000000)
  B := (90248579840011541874922329/1000000000000000000000000000)
  C := (45983219939376863277802343/10000000000000000000000000000)
  dδ := (78749696266819824153060381/1000000000000000000000000000)
  dM := (2548616986067713668928647/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(11096274557068224186906491/1250000000000000000000000), (24476458847350112790763887/1000000000000000000000000), (25690736611618017803948533/1000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1549/2954)
  hi := (2326/4431)
  vmin := (4896230/19633761)
  damping := (4896230/19633761)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell119
