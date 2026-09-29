import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 73
  A := (-16558362669548495793492293/10000000000000000000000000)
  B := (464831374627175275549007/4000000000000000000000000)
  C := (-20311726177467547709877549/25000000000000000000000000000)
  dδ := (71960702942682225335957469/1000000000000000000000000000)
  dM := (14215511467870185855627563/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(4660939068567480636495759/2500000000000000000000000), (10798623127855877967817833/1000000000000000000000000), (1465250668596667793508459/25000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (49/99)
  hi := (131/264)
  vmin := (2450/9801)
  damping := (2450/9801)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell062
