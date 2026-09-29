import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 44
  A := (-21439723926258871300021269/50000000000000000000000000)
  B := (79782315784132293301489369/1000000000000000000000000000)
  C := (510833058341320436768207/2500000000000000000000000)
  dδ := (14862186165368447554602227/250000000000000000000000000)
  dM := (5890589795684231721670243/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(32252889011627363657908063/10000000000000000000000000), (5693692167634289286182181/25000000000000000000000000), (7288900610463929119475779/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (27/47)
  hi := (653/1128)
  vmin := (310175/1272384)
  damping := (310175/1272384)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell169
