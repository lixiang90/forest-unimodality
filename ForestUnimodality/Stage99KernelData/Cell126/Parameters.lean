import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 50
  A := (-17062561006429931037331471/25000000000000000000000000)
  B := (23900180867374679061221343/250000000000000000000000000)
  C := (50597223204914354779959673/10000000000000000000000000000)
  dδ := (9222014776086134846266873/100000000000000000000000000)
  dM := (15956232585525287857863841/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(9230200026792175771461757/1250000000000000000000000), (10461546778217170938773961/250000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23557/44732)
  hi := (11791/22366)
  vmin := (124689825/500237956)
  damping := (124689825/500237956)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell126
