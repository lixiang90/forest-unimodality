import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell176
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 5) where
  terms := Finset.univ
  scale := 29
  A := (24751153607227479136554393/10000000000000000000000000)
  B := (-16339508016870264717201877/1000000000000000000000000000)
  C := (6139958945638902126917813/50000000000000000000000000)
  dδ := (46636271581924668150342939/1000000000000000000000000000)
  dM := (14210790656247264699893473/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(792587323904892226966723/312500000000000000000000), (44065549852655860885164429/100000000000000000000000000), (16488653779793911446915899/10000000000000000000000000), (8045757848201030570933767/5000000000000000000000000), (73328739499163342330234627/10000000000000000000000000)]
  retention := ![(19/20), (4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (63/103)
  hi := (129/209)
  vmin := (10320/43681)
  damping := (10320/43681)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell176
