import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 61
  A := (-64260591729424736517017891/100000000000000000000000000)
  B := (13157030025241772674959861/100000000000000000000000000)
  C := (-5577604272464544571397127/12500000000000000000000000)
  dδ := (6067361864101420559913791/50000000000000000000000000)
  dM := (24890071496349078748744343/10000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(6665341650573831655535173/1250000000000000000000000), (21026644252244487631742231/1000000000000000000000000)]
  retention := ![(3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4/9)
  hi := (301/666)
  vmin := (20/81)
  damping := (20/81)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell026
