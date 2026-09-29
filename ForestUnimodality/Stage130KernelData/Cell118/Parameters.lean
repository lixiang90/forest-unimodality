import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 89
  A := (-579876468343228586462601/400000000000000000000000)
  B := (92250434421875915358413067/1000000000000000000000000000)
  C := (35580488768975158248020207/10000000000000000000000000000)
  dδ := (62405038243330157587962503/1000000000000000000000000000)
  dM := (24594671535622437703177967/25000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(13844586229363647689183381/1000000000000000000000000), (73646885610370134145341581/1000000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2294/4389)
  hi := (1531/2926)
  vmin := (2135745/8561476)
  damping := (2135745/8561476)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell118
