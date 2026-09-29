import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell174
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 32
  A := (-19618718253738236633409997/100000000000000000000000000)
  B := (65250058227878424133017177/1000000000000000000000000000)
  C := (14507959451707816422860731/100000000000000000000000000)
  dδ := (2044139749778476067287869/40000000000000000000000000)
  dM := (99031760236909936907789831/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(10761853184180316667095667/5000000000000000000000000), (9213553643936547743464871/1000000000000000000000000), (10417154484284687487871679/10000000000000000000000000)]
  retention := ![(7/10), (1/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3/5)
  hi := (123/203)
  vmin := (9840/41209)
  damping := (9840/41209)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell174
