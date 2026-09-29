import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 74
  A := (-14874348863731049929981509/10000000000000000000000000)
  B := (2168048101387147486018847/20000000000000000000000000)
  C := (15946869143343195187462191/5000000000000000000000000000)
  dδ := (36118351313732123541999641/500000000000000000000000000)
  dM := (1658733951308629273480727/1250000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(54972607225916370055074367/10000000000000000000000000), (20964914483009056134221737/2500000000000000000000000), (29280150634516424190678663/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22331/43056)
  hi := (27/52)
  vmin := (675/2704)
  damping := (675/2704)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell103
