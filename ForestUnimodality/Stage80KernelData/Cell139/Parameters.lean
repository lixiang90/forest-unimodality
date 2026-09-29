import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 33
  A := (18157099994086586458763577/20000000000000000000000000)
  B := (23929844115384794195344753/500000000000000000000000000)
  C := (16252890481149714560493713/2500000000000000000000000000)
  dδ := (1652768944094787639809141/10000000000000000000000000)
  dM := (19790114405578125914009213/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(1714755358298007958950393/250000000000000000000000), (26890067828295272533978277/1000000000000000000000000)]
  retention := ![(7/10), (1/20)]
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
end ForestUnimodality.Stage80KernelData.Cell139
