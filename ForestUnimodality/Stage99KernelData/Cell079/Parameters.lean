import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 62
  A := (-19232231547440531227266547/20000000000000000000000000)
  B := (18507510306468658023426599/200000000000000000000000000)
  C := (24081523990758689143798499/10000000000000000000000000000)
  dδ := (77322866539422177578622097/1000000000000000000000000000)
  dM := (12750026785353046725191017/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(41318157660029477540319931/5000000000000000000000000), (2649059500360404495467037/250000000000000000000000), (842072283500802285516329/20000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3579/7004)
  hi := (5381/10506)
  vmin := (27577625/110376036)
  damping := (27577625/110376036)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell079
