import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 45
  A := (-7387983818377968259127897/10000000000000000000000000)
  B := (2936827208448515580396787/25000000000000000000000000)
  C := (-6927322246282260898020411/25000000000000000000000000)
  dδ := (83049969011999014156799603/1000000000000000000000000000)
  dM := (19968507642396629737924219/10000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(8130239873126512861745141/2000000000000000000000000), (14247713528618001888048639/1000000000000000000000000)]
  retention := ![(9/20), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (65/153)
  hi := (22/51)
  vmin := (5720/23409)
  damping := (5720/23409)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell023
