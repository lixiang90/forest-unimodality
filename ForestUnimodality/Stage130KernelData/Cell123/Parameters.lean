import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 73
  A := (-156220840131555375495509/80000000000000000000000)
  B := (13104926781778361566388469/100000000000000000000000000)
  C := (45586541643888468106071699/10000000000000000000000000000)
  dδ := (71355621560861948182719061/1000000000000000000000000000)
  dM := (15732718687897517669753/9765625000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(41400335374047164682664857/100000000000000000000000000), (15643992292904954410914797/1000000000000000000000000), (27461228442156823348341277/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1549/2954)
  hi := (2326/4431)
  vmin := (4896230/19633761)
  damping := (4896230/19633761)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell123
