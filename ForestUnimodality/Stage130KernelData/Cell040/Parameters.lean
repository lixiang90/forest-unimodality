import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 77
  A := (-12534315175511331796798231/10000000000000000000000000)
  B := (3834595298781348082783893/40000000000000000000000000)
  C := (-39885918779631107308758509/10000000000000000000000000000)
  dδ := (7199631432560907318141119/100000000000000000000000000)
  dM := (2304231765578702764013519/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(2262966799940390738576923/312500000000000000000000), (8570559210794619353634971/2500000000000000000000000), (6500885331587404891706683/100000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23/48)
  hi := (2983/6208)
  vmin := (575/2304)
  damping := (575/2304)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell040
