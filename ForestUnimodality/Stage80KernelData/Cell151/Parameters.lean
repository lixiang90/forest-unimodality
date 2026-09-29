import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (459837353902015796869307/2500000000000000000000000)
  B := (33660291499765154776824261/500000000000000000000000000)
  C := (69207914301644040191985319/10000000000000000000000000000)
  dδ := (5971431071253136685372809/50000000000000000000000000)
  dM := (16268054056882052995497423/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(9130238669232831894007063/1250000000000000000000000), (9292519432928699529838923/500000000000000000000000), (13182207310322121784906813/1000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95449/180624)
  hi := (47737/90312)
  vmin := (2032402775/8156257344)
  damping := (2032402775/8156257344)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell151
