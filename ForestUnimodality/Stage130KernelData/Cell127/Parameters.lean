import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 73
  A := (-19804063613625130690820697/10000000000000000000000000)
  B := (6634112637027808623280123/50000000000000000000000000)
  C := (24082371067143839953039741/5000000000000000000000000000)
  dδ := (7197829044771179851647247/100000000000000000000000000)
  dM := (16321602190849883364659467/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(2057709573089667287604243/125000000000000000000000), (54490765237574507295903459/1000000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4657/8862)
  hi := (111/211)
  vmin := (11100/44521)
  damping := (11100/44521)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell127
