import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell044.Parameters
import ForestUnimodality.BinomialMassData.Q4487_9312.Batch000_049
import ForestUnimodality.BinomialMassData.Q4487_9312.Batch050_099
import ForestUnimodality.BinomialMassData.Q8999_18624.Batch000_049
import ForestUnimodality.BinomialMassData.Q8999_18624.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree000.table
  base := (398818847649760205753466383/10000000000000000000000000)
  polynomial :=
    { denominator := 250000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (30593038492365921821036777500000000000)
      linear := (1061729736374056754649730650000000000)
      constant := (9970471191244005143836659575000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree000.table
  base := (398818847649760205753466383/10000000000000000000000000)
  polynomial :=
    { denominator := 250000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (30593038492365921821036777500000000000)
      linear := (1061729736374056754649730650000000000)
      constant := (9970471191244005143836659575000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree001.table
  base := (11473543642274840070226077479943055648419/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42340500000000000000000000000000000000000000
      center := (338724)
      previous := (169362)
      next := (169362)
      square := (5181298185144077251454430710955000000000000)
      linear := (-4813414633530286292718847068525637500000000)
      constant := (972707501945054357645860111144016613918456839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree001.table
  base := (45799632562376772395734436294342669329071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20725192740576309005817722843820000000000000)
      linear := (-19309299622879135691187398913180675000000000)
      constant := (3882849978678581275561005673826573384384748851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (4996705188371811201/10000000000000000000)
  directionHi := (49967051883718112011/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree002.table
  base := (68102606699797318377392828761257346573729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-98066459386723555855186818193965750000000000)
      constant := (5813383847096418149207216622874289669897445449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree002.table
  base := (67842123713940254552560289800948112766531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-98344664830513508456746871389356375000000000)
      constant := (5791589540619844300062231666425461947729486611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4996705188371811201/10000000000000000000)
  centralHi := (49967051883718112011/100000000000000000000)
  directionLo := (1413281648915085213/2000000000000000000)
  directionHi := (70664082445754260651/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree003.table
  base := (42005462708501580966709262777609245143107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5756997983493419168282700789950000000000000)
      linear := (-16444308048682694309242796189186125000000000)
      constant := (406970559095989767016020136772081760598368763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree003.table
  base := (83572736832621803882479975472465506932809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-32981351245295372819005610110169125000000000)
      constant := (809950833017995268398473476439108156879237381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1413281648915085213/2000000000000000000)
  centralHi := (70664082445754260651/100000000000000000000)
  directionLo := (21636368141757486827/25000000000000000000)
  directionHi := (86545472567029947309/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree004.table
  base := (54084355504512058896467676524335607348087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-395862170979129883422367026422769000000000000)
      constant := (4957944974515582734259050151870944253343355247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree004.table
  base := (26873958907599114027559628080395662476629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-198487496377144846914303619602165750000000000)
      constant := (2465791815373341954392661980517397898870920349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21636368141757486827/25000000000000000000)
  centralHi := (86545472567029947309/100000000000000000000)
  directionLo := (4996705188371811201/5000000000000000000)
  directionHi := (99934103767436224021/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree005.table
  base := (36321448992238650303026908569151020463177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-495726797081971269278363721440187750000000000)
      constant := (3668570973055802082421218235901788091186041537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree005.table
  base := (36069785852702366231614002378548788246583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-497117824300921032286163987417140875000000000)
      constant := (3650591758989545236960440102344750928719832523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4996705188371811201/5000000000000000000)
  centralHi := (99934103767436224021/100000000000000000000)
  directionLo := (27932431161813153913/25000000000000000000)
  directionHi := (111729724647252615653/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree006.table
  base := (25270666858732748910550919194302774107971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-66176824798312517237151157384178500000000000)
      constant := (332856253719227838320987550375584160956899139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree006.table
  base := (12540192471528983169939125430976614618973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5756997983493419168282700789950000000000000)
      linear := (-33181147547086242819095596423886125000000000)
      constant := (165799817204373461021961014263404964996791957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27932431161813153913/25000000000000000000)
  centralHi := (111729724647252615653/100000000000000000000)
  directionLo := (24478756213256478571/20000000000000000000)
  directionHi := (15299222633285299107/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree007.table
  base := (17991628161856258409267018060796296153437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-695456049287654040990357111475025250000000000)
      constant := (2690356507206131988054198113709952963162948597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree007.table
  base := (3568546625738289489052290856693062452629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20725192740576309005817722843820000000000000)
      linear := (-139480697478836741840255496768551925000000000)
      constant := (536858382732985337192551085196210527605763849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24478756213256478571/20000000000000000000)
  centralHi := (15299222633285299107/12500000000000000000)
  directionLo := (132200393031379615791/100000000000000000000)
  directionHi := (8262524564461225987/6250000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree008.table
  base := (3222475240860309084027774551945113627551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25906490925720386257272153554775000000000000)
      linear := (-198830168847623856711588451623111000000000000)
      constant := (654375888324761719050604268834759979594646231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree008.table
  base := (3191961840962231205601405028362428878937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25906490925720386257272153554775000000000000)
      linear := (-199386579735203761914708558013892250000000000)
      constant := (653930174412668421808692861165498011772264097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132200393031379615791/100000000000000000000)
  centralHi := (8262524564461225987/6250000000000000000)
  directionLo := (141328164891508521301/100000000000000000000)
  directionHi := (70664082445754260651/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree009.table
  base := (9094882841888248779652991926612297587189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-99465033499259645855816722389984750000000000)
      constant := (300380437565370394031080756281324947841611301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree009.table
  base := (561872409005414288927841672549156857597/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (188180)
      previous := (94090)
      next := (94090)
      square := (2878498991746709584141350394975000000000000)
      linear := (-24935809735762399614344193896343843750000000)
      constant := (75149135225071122990929383399068912951505067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141328164891508521301/100000000000000000000)
  centralHi := (70664082445754260651/50000000000000000000)
  directionLo := (14990115565115433603/10000000000000000000)
  directionHi := (149901155651154336031/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree010.table
  base := (6126042767124249368883242858273998070371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-995049927596178198558347196527281500000000000)
      constant := (2907425813416376358542675533350618164972086651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree010.table
  base := (6032124956000571598592895904214672931373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-997831982034077724573947728481187750000000000)
      constant := (2912848523787823863131934345151814495845347013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14990115565115433603/10000000000000000000)
  centralHi := (149901155651154336031/100000000000000000000)
  directionLo := (39502422979089030541/25000000000000000000)
  directionHi := (31601938383271224433/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree011.table
  base := (74271927140020672806677356199697177839/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84681000000000000000000000000000000000000000
      center := (677448)
      previous := (338724)
      next := (338724)
      square := (10362596370288154502908861421910000000000000)
      linear := (-109491455369901958441434389154470025000000000)
      constant := (320666356801848321082033097104725861317296795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree011.table
  base := (453374824699581035704323002069928784223/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25906490925720386257272153554775000000000000)
      linear := (-274493703395177265757876119173499281250000000)
      constant := (803880092137400287203022205853326456243810101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39502422979089030541/25000000000000000000)
  centralHi := (31601938383271224433/20000000000000000000)
  directionLo := (41430490744628492591/25000000000000000000)
  directionHi := (33144392595702794073/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree012.table
  base := (1702094193609884171203955158298756238043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-132753242200206774474482287395791000000000000)
      constant := (398663732192969555892498791381867184943746587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree012.table
  base := (810345539561633674025056996495159744823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5756997983493419168282700789950000000000000)
      linear := (-66562091395963355638281179161489250000000000)
      constant := (200019609980852098822046910905378137726539607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41430490744628492591/25000000000000000000)
  centralHi := (33144392595702794073/20000000000000000000)
  directionLo := (173090945134059894617/100000000000000000000)
  directionHi := (86545472567029947309/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree013.table
  base := (-146741549389875896132716101976211009/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84681000000000000000000000000000000000000000
      center := (677448)
      previous := (338724)
      next := (338724)
      square := (10362596370288154502908861421910000000000000)
      linear := (-129464380590470235612633728157953775000000000)
      constant := (404348023289119511815131435348773398959921871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree013.table
  base := (-39422301040880321756254678291325905821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-649130238336985869973308986559807937500000000)
      constant := (2029775862436298445009622379555152906262140649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173090945134059894617/100000000000000000000)
  centralHi := (86545472567029947309/50000000000000000000)
  directionLo := (180158767650515167581/100000000000000000000)
  directionHi := (90079383825257583791/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree014.table
  base := (-1455619222529333007930011437977972746101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-1394508432007543741982333976596956500000000000)
      constant := (4568227054853231904963151921849940399262421219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree014.table
  base := (-382394097306904377392663080721028118961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25906490925720386257272153554775000000000000)
      linear := (-349600827055150769601043680333106312500000000)
      constant := (1147051955200620439184014704247237882506701059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180158767650515167581/100000000000000000000)
  centralHi := (90079383825257583791/50000000000000000000)
  directionLo := (23369948597003832039/12500000000000000000)
  directionHi := (186959588776030656313/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree015.table
  base := (-1349768848801779928985400538183410633551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5756997983493419168282700789950000000000000)
      linear := (-83020725450576951546573926200798625000000000)
      constant := (286605364053205196252455875254833490520793641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree015.table
  base := (-692591089958523360430078046098708690261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (94090)
      previous := (47045)
      next := (47045)
      square := (1439249495873354792070675197487500000000000)
      linear := (-20813140830100478011968492632572703125000000)
      constant := (71986535516951930912954804505468241055534313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23369948597003832039/12500000000000000000)
  centralHi := (186959588776030656313/100000000000000000000)
  directionLo := (48380389951180546659/25000000000000000000)
  directionHi := (193521559804722186637/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree016.table
  base := (-1880625020187799143535877650304176918469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-797118842106613256847163683315897000000000000)
      constant := (2906557677955127307409734504257818994367126611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree016.table
  base := (-765813676210603730881693249681268795557/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20725192740576309005817722843820000000000000)
      linear := (-319737794262773151063857643551608800000000000)
      constant := (1168332146543296912523944319193167527123437683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48380389951180546659/25000000000000000000)
  centralHi := (193521559804722186637/100000000000000000000)
  directionLo := (4996705188371811201/2500000000000000000)
  directionHi := (199868207534872448041/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree017.table
  base := (-291382292403784995061166316595836370499/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12953245462860193128636076777387500000000000)
      linear := (-211762788789508487443790507706151593750000000)
      constant := (816134330167504985526145337314227241381267112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree017.table
  base := (-4726968848729862413160063675040452874123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-1698831802860497093776844965970853375000000000)
      constant := (6562296302089728184523067611877049143564827737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4996705188371811201/2500000000000000000)
  centralHi := (199868207534872448041/100000000000000000000)
  directionLo := (103009716358643835141/50000000000000000000)
  directionHi := (206019432717287670283/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree018.table
  base := (-5419306193024696671704424594473055236907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-199329659602101031711813417407403500000000000)
      constant := (811702284069478884728013545853737507650942037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree018.table
  base := (-68515044956076834768007685470075268393/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2352250000000000000000000000000000000000000
      center := (18818)
      previous := (9409)
      next := (9409)
      square := (287849899174670958414135039497500000000000)
      linear := (-4997151762242023422873338094954618750000000)
      constant := (20398572267920460504406836356125500845474276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103009716358643835141/50000000000000000000)
  centralHi := (206019432717287670283/100000000000000000000)
  directionLo := (414047358080591371/195312500000000000)
  directionHi := (211992247337262781953/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree019.table
  base := (-755898098296855446221985233272320933131/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12953245462860193128636076777387500000000000)
      linear := (-236728945315218833907789681460506281250000000)
      constant := (1017579569673564969078537956688558383542002539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree019.table
  base := (-3053067275347282759057664969789699423401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-949558732976879885345979231198236062500000000)
      constant := (4092006846757115636807718579854825200919948669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414047358080591371/195312500000000000)
  centralHi := (211992247337262781953/100000000000000000000)
  directionLo := (217801329667780900787/100000000000000000000)
  directionHi := (54450332416945225197/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree020.table
  base := (-409882279348817125922183884187831278721/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12953245462860193128636076777387500000000000)
      linear := (-249212023578074007139789268337683625000000000)
      constant := (1129246955851030546111175735300508292410753998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree020.table
  base := (-3307067280865386856074801705032619938751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-999630148750195554574757605304640750000000000)
      constant := (4541415793967831906010658630369724078154126569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217801329667780900787/100000000000000000000)
  centralHi := (54450332416945225197/25000000000000000000)
  directionLo := (27932431161813153913/12500000000000000000)
  directionHi := (44691889858901046261/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree021.table
  base := (-6962941239212876210991013063906100624051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-232617868303048160330478982413209750000000000)
      constant := (1109379987014998108966990712456937932822054141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree021.table
  base := (-1403211594664954365600211364450150810253/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2302799193397367667313080315980000000000000)
      linear := (-46653402867711609946823821307157575000000000)
      constant := (223089345400761405054963678641233499581017023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27932431161813153913/12500000000000000000)
  centralHi := (44691889858901046261/20000000000000000000)
  directionLo := (114488898755462020823/50000000000000000000)
  directionHi := (228977797510924041647/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree022.table
  base := (-1454255088034095178080479785266786634193/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20725192740576309005817722843820000000000000)
      linear := (-438685088166054965766061507347261300000000000)
      constant := (2198230988933247914572852263080961137904902567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree022.table
  base := (-7321536805519506719624686071664229355919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-2199545960593653786064628707034900250000000000)
      constant := (11051764909720772737431818986628597421255173161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114488898755462020823/50000000000000000000)
  centralHi := (228977797510924041647/100000000000000000000)
  directionLo := (234366247627306415361/100000000000000000000)
  directionHi := (117183123813653207681/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree023.table
  base := (-1498342461507304788043139834060603968741/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20725192740576309005817722843820000000000000)
      linear := (-458658013386623242937260846350745050000000000)
      constant := (2410690629532396037118440985088007782041793379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree023.table
  base := (-1884794780562768058516818347605278458127/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12953245462860193128636076777387500000000000)
      linear := (-287461099017535640565273181905963703125000000)
      constant := (1515041968566627497354363629732618715134103444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234366247627306415361/100000000000000000000)
  centralHi := (117183123813653207681/50000000000000000000)
  directionLo := (239633562550937525583/100000000000000000000)
  directionHi := (14977097659433595349/6250000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree024.table
  base := (-1907991260440570808642176549495534487557/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (188180)
      previous := (94090)
      next := (94090)
      square := (2878498991746709584141350394975000000000000)
      linear := (-66476519250998822237286136854754000000000000)
      constant := (365851703627633095206719023439169078506576187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree024.table
  base := (-383835554110473036455909756056988989687/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704500000000000000000000000000000000000000
      center := (37636)
      previous := (18818)
      next := (18818)
      square := (575699798349341916828270078995000000000000)
      linear := (-13332397909371758127665234463669550000000000)
      constant := (73578215559038765049070408413796099971035017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239633562550937525583/100000000000000000000)
  centralHi := (14977097659433595349/6250000000000000000)
  directionLo := (24478756213256478571/10000000000000000000)
  directionHi := (244787562132564785711/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree025.table
  base := (-7698975566782550887653298524014768023689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-2493019319138798986398297621788562750000000000)
      constant := (14342191644403950743986418606016424862579741791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree025.table
  base := (-7741085315462796180512287382677885535101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-2499974455233547801437298951673328375000000000)
      constant := (14422405310335847121035910759114656880275549719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24478756213256478571/10000000000000000000)
  centralHi := (244787562132564785711/100000000000000000000)
  directionLo := (4996705188371811201/2000000000000000000)
  directionHi := (249835259418590560051/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree026.table
  base := (-3849500877692437232631883714960687022931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-1296441972620820186127147158402990750000000000)
      constant := (7783757083081967909903389916024309304398679989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree026.table
  base := (-3869284056959626982885245048940410880697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-1300058643390089569947427849943068875000000000)
      constant := (7827392320897276008150385029074277923633572343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4996705188371811201/2000000000000000000)
  centralHi := (249835259418590560051/100000000000000000000)
  directionLo := (31847871573972721311/12500000000000000000)
  directionHi := (254782972591781770489/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree027.table
  base := (-1527538059578675226074526677050871571081/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2302799193397367667313080315980000000000000)
      linear := (-59838857140988483513562022484964450000000000)
      constant := (374358905077586881467117611467211136106448871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree027.table
  base := (-191870311030474965573611636758188921737/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704500000000000000000000000000000000000000
      center := (37636)
      previous := (18818)
      next := (18818)
      square := (575699798349341916828270078995000000000000)
      linear := (-15001445101815613768624513600549706250000000)
      constant := (94115211646605997896558325580687357071925009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31847871573972721311/12500000000000000000)
  centralHi := (254782972591781770489/100000000000000000000)
  directionLo := (129818208850544920963/50000000000000000000)
  directionHi := (259636417701089841927/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree028.table
  base := (-752013934377024829196783873651008159617/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84681000000000000000000000000000000000000000
      center := (677448)
      previous := (338724)
      next := (338724)
      square := (10362596370288154502908861421910000000000000)
      linear := (-279261319744732314396628770684081900000000000)
      constant := (1817766961499176436724144871210041396785472823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree028.table
  base := (-1510984159063785968806888681321620264889/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20725192740576309005817722843820000000000000)
      linear := (-560080589974688363361993839262351300000000000)
      constant := (3655966717897988342691364985904042696223934591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129818208850544920963/50000000000000000000)
  centralHi := (259636417701089841927/100000000000000000000)
  directionLo := (264400786062759231583/100000000000000000000)
  directionHi := (8262524564461225987/3125000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree029.table
  base := (-7350953380308674609669397796407992982127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-2892477823550164529822284401858237750000000000)
      constant := (19561680913076525837989965988260961586124253513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree029.table
  base := (-295340013391980138087368703687356716223/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20725192740576309005817722843820000000000000)
      linear := (-580109156284014631053505188904913175000000000)
      constant := (3934336196460277342594021888011892268434788185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264400786062759231583/100000000000000000000)
  centralHi := (8262524564461225987/3125000000000000000)
  directionLo := (269080809320462603013/100000000000000000000)
  directionHi := (134540404660231301507/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree030.table
  base := (-1783572973201677045839706332089280361347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (188180)
      previous := (94090)
      next := (94090)
      square := (2878498991746709584141350394975000000000000)
      linear := (-83120623601472386546618919357657125000000000)
      constant := (583273122038088045658743827578497332173836077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree030.table
  base := (-3582355892511203483599550927885544050337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5756997983493419168282700789950000000000000)
      linear := (-166704922942594694095837927374298625000000000)
      constant := (1173107107802170086614206575322886742202254167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269080809320462603013/100000000000000000000)
  centralHi := (134540404660231301507/50000000000000000000)
  directionLo := (273680814487434123783/100000000000000000000)
  directionHi := (34210101810929265473/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree031.table
  base := (-3436956417199330532469298379461028413567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-1546103537877923650767138895946537625000000000)
      constant := (11242902914323164552774365302099162525957607873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree031.table
  base := (-1380462627640808928536578588677399810269/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20725192740576309005817722843820000000000000)
      linear := (-620166288902667166436527888190036925000000000)
      constant := (4522451246672817784622845712905643034596298311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273680814487434123783/100000000000000000000)
  centralHi := (34210101810929265473/12500000000000000000)
  directionLo := (5564095415876888411/2000000000000000000)
  directionHi := (278204770793844420551/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree032.table
  base := (-6573211636788495045553939747297170067361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-3192071701858688687390274486910494000000000000)
      constant := (24025313690349881035055855398969986341525803159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree032.table
  base := (-329984943622539099542713659733179734319/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42340500000000000000000000000000000000000000
      center := (338724)
      previous := (169362)
      next := (169362)
      square := (5181298185144077251454430710955000000000000)
      linear := (-160048713802998358532009809458149700000000000)
      constant := (1208018920663797183360272491350292506918132761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5564095415876888411/2000000000000000000)
  centralHi := (278204770793844420551/100000000000000000000)
  directionLo := (141328164891508521301/50000000000000000000)
  directionHi := (282656329783017042603/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree033.table
  base := (-3117628158046954185656943920970473164031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5756997983493419168282700789950000000000000)
      linear := (-182885351553418337402570621218217375000000000)
      constant := (1423116454211609034836521839290215269171507321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree033.table
  base := (-1564983810522140762850404475808398236027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (94090)
      previous := (47045)
      next := (47045)
      square := (1439249495873354792070675197487500000000000)
      linear := (-45848848716758312626357679685775046875000000)
      constant := (357778261481834035057007372708399362056228166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141328164891508521301/50000000000000000000)
  centralHi := (282656329783017042603/100000000000000000000)
  directionLo := (8969964369026084619/3125000000000000000)
  directionHi := (287038859808834707809/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree034.table
  base := (-91606548706126856867413767460424781759/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12953245462860193128636076777387500000000000)
      linear := (-423975119258046432387783484618166437500000000)
      constant := (3407239816069390775157564719925202416118803968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree034.table
  base := (-5885792083076804969876363462391657144843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-3401259939153229847555309685588612750000000000)
      constant := (27410990921133530090509030403304341577411299917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8969964369026084619/3125000000000000000)
  centralHi := (287038859808834707809/100000000000000000000)
  directionLo := (9104858620662486421/3125000000000000000)
  directionHi := (291355475861199565473/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree035.table
  base := (-545840506629734572807890193626337951967/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84681000000000000000000000000000000000000000
      center := (677448)
      previous := (338724)
      next := (338724)
      square := (10362596370288154502908861421910000000000000)
      linear := (-349166558016721284495826457196275025000000000)
      constant := (2895056862046352545499141634987388472373857473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree035.table
  base := (-342485719047279885096934686600897724243/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25906490925720386257272153554775000000000000)
      linear := (-875350692674965296503216608450355531250000000)
      constant := (7278258703869819912670815651812575677212498443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9104858620662486421/3125000000000000000)
  centralHi := (291355475861199565473/100000000000000000000)
  directionLo := (295609065470354309301/100000000000000000000)
  directionHi := (147804532735177154651/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree036.table
  base := (-2512138874600684851196495954872425603803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5756997983493419168282700789950000000000000)
      linear := (-199529455903891901711903403721120500000000000)
      constant := (1705214153823651478318030579174689441243817573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree036.table
  base := (-5044133787364352674581638026468116669141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-400171733582943613830047020223803500000000000)
      constant := (3429552789659841031131034268569008974635052331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295609065470354309301/100000000000000000000)
  centralHi := (147804532735177154651/50000000000000000000)
  directionLo := (14990115565115433603/5000000000000000000)
  directionHi := (299802311302308672061/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree037.table
  base := (-456248259303520815393956358134035792719/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84681000000000000000000000000000000000000000
      center := (677448)
      previous := (338724)
      next := (338724)
      square := (10362596370288154502908861421910000000000000)
      linear := (-369139483237289561667025796199758775000000000)
      constant := (3248760376482684798173176393622310442771137361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree037.table
  base := (-4580920765305581293355440194720851781489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-3701688433793123862927979930227040875000000000)
      constant := (32669638890932136236062489947893917229002667491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14990115565115433603/5000000000000000000)
  centralHi := (299802311302308672061/100000000000000000000)
  directionLo := (30393771094774760749/10000000000000000000)
  directionHi := (303937710947747607491/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree038.table
  base := (-15917452725748799692215947043683403621/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12953245462860193128636076777387500000000000)
      linear := (-473907432309467125315781832126875812500000000)
      constant := (4291457386571899574379274775071331154131918168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree038.table
  base := (-1022994236127695805865636629919910614867/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25906490925720386257272153554775000000000000)
      linear := (-950457816334938800346384169609962562500000000)
      constant := (8630967493213317438346056185275514946683385073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30393771094774760749/10000000000000000000)
  centralHi := (303937710947747607491/100000000000000000000)
  directionLo := (308017594319069302059/100000000000000000000)
  directionHi := (15400879715953465103/5000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree039.table
  base := (-3563103837509514375338930564695478423949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-432347120508730932042472372448047250000000000)
      constant := (4025097702229222451056056809974027583352813859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree039.table
  base := (-3578968575728387077270988290253189804657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-433552677431820726649232602961406625000000000)
      constant := (4047614139213593572091175059907714525213919787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308017594319069302059/100000000000000000000)
  centralHi := (15400879715953465103/5000000000000000000)
  directionLo := (312044138999688522121/100000000000000000000)
  directionHi := (156022069499844261061/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree040.table
  base := (-1514349814210705425880607517892454286783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-1995494355340709887119124023524922000000000000)
      constant := (19085068322675229955484517110364744703540928777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree040.table
  base := (-1521700441415850601869660093536008065437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-2001058464216508939150325087432734500000000000)
      constant := (19191741633638268899036691486592778394760729403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312044138999688522121/100000000000000000000)
  centralHi := (156022069499844261061/50000000000000000000)
  directionLo := (316019383832712244329/100000000000000000000)
  directionHi := (31601938383271224433/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree041.table
  base := (-2473019041597495169954509177703671095751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-4090853336784261160094244742067262750000000000)
      constant := (40164315582939581908825149500243395736534459569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree041.table
  base := (-621658406316373239298443522430710983121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12953245462860193128636076777387500000000000)
      linear := (-512782469997456152094775865384784796875000000)
      constant := (5048577858765789294601368425169394340872094987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316019383832712244329/100000000000000000000)
  centralHi := (31601938383271224433/10000000000000000000)
  directionLo := (319945240989700121463/100000000000000000000)
  directionHi := (39993155123712515183/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree042.table
  base := (-1897294420097979106299565016803249084319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-465635329209678060661137937453853500000000000)
      constant := (4689812419643076251070795407329388588740642529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree042.table
  base := (-11936844725386383900145715959575112433/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2352250000000000000000000000000000000000000
      center := (18818)
      previous := (9409)
      next := (9409)
      square := (287849899174670958414135039497500000000000)
      linear := (-11673340532017445986710454642475243750000000)
      constant := (117899561231412677859829902544912873158315362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319945240989700121463/100000000000000000000)
  centralHi := (39993155123712515183/12500000000000000000)
  directionLo := (64764701344453821077/20000000000000000000)
  directionHi := (161911753361134552693/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree043.table
  base := (-65131967250464256178247637960351901769/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42340500000000000000000000000000000000000000
      center := (338724)
      previous := (169362)
      next := (169362)
      square := (5181298185144077251454430710955000000000000)
      linear := (-214529129449497196590311906605105012500000000)
      constant := (2215101546386739681141767821213402941973486811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree043.table
  base := (-657147560523984423519866998469480930239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-2151272711536455946836660209751948562500000000)
      constant := (22274523410452493364326645061920063396576899991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64764701344453821077/20000000000000000000)
  centralHi := (161911753361134552693/50000000000000000000)
  directionLo := (65531174193617999663/20000000000000000000)
  directionHi := (81913967742022499579/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree044.table
  base := (-17251502017651450926017580071265602707/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21170250000000000000000000000000000000000000
      center := (169362)
      previous := (84681)
      next := (84681)
      square := (2590649092572038625727215355477500000000000)
      linear := (-109761180377319632941555870677987975000000000)
      constant := (1161134695607684867520404191928852424684668533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree044.table
  base := (-175208982671431331805654015562215163623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25906490925720386257272153554775000000000000)
      linear := (-1100672063654885808032719291929176625000000000)
      constant := (11676038079448816901653367725488896678822990737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65531174193617999663/20000000000000000000)
  centralHi := (81913967742022499579/25000000000000000000)
  directionLo := (331443925957027940729/100000000000000000000)
  directionHi := (33144392595702794073/10000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree045.table
  base := (-60465917057014355424226846541047232209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-498923537910625189279803502459659750000000000)
      constant := (5404256162992235190100731889574792532685895519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree045.table
  base := (-35211561609914888769076366822438339947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5756997983493419168282700789950000000000000)
      linear := (-250157282564787476143801884218306437500000000)
      constant := (2717171214005294662640578730394577763108657427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331443925957027940729/100000000000000000000)
  centralHi := (33144392595702794073/10000000000000000000)
  directionLo := (83797293485439461739/25000000000000000000)
  directionHi := (335189173941757846957/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree046.table
  base := (117064297017185212771442008025515843679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20725192740576309005817722843820000000000000)
      linear := (-918035293459693617874845643430871300000000000)
      constant := (10176142855308071645531963215269933429033581399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree046.table
  base := (23045010947487859683524215591089438879/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20725192740576309005817722843820000000000000)
      linear := (-920594783542561181809198132828465050000000000)
      constant := (10232753230480921144871664661799707660587312995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83797293485439461739/25000000000000000000)
  centralHi := (335189173941757846957/100000000000000000000)
  directionLo := (338893034159317260209/100000000000000000000)
  directionHi := (33889303415931726021/10000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree047.table
  base := (623279824520942897811974179002165825567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-2345020546700654737615112456085887625000000000)
      constant := (26586275689735152934917108087754250339821714127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree047.table
  base := (619035143015463179471596493378914278231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-2351558374629718623751773706177567312500000000)
      constant := (26734071320832752051959366385637207050444098061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338893034159317260209/100000000000000000000)
  centralHi := (33889303415931726021/10000000000000000000)
  directionLo := (342556849115089732303/100000000000000000000)
  directionHi := (21409803069693108269/6250000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree048.table
  base := (384515530258712088943140321451986710327/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2302799193397367667313080315980000000000000)
      linear := (-106442349322314463579693813493093200000000000)
      constant := (1233639110249902017420960424056835342957466743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree048.table
  base := (1914744353812548959681558302310664373761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-533695508978452065106789351174216000000000000)
      constant := (6202461643358859973721408985085115291092717249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342556849115089732303/100000000000000000000)
  centralHi := (21409803069693108269/6250000000000000000)
  directionLo := (173090945134059894617/50000000000000000000)
  directionHi := (69236378053623957847/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree049.table
  base := (2612769225883443855665776908849357611133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-4889770345606992246942218302206612750000000000)
      constant := (57904288682658665391235749777806524447962103573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree049.table
  base := (1302772214836825057255550337305449528653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-2451701206176349962209330454390376687500000000)
      constant := (29112875765721977415960596358164709606985083443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173090945134059894617/50000000000000000000)
  centralHi := (69236378053623957847/20000000000000000000)
  directionLo := (34976936318602678407/10000000000000000000)
  directionHi := (349769363186026784071/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree050.table
  base := (331658653334055507235191457320126571893/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84681000000000000000000000000000000000000000
      center := (677448)
      previous := (338724)
      next := (338724)
      square := (10362596370288154502908861421910000000000000)
      linear := (-498963497170983363279821499722403150000000000)
      constant := (6034409115211528755336641918848271224171971133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree050.table
  base := (413740718058653817544083289988085714807/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12953245462860193128636076777387500000000000)
      linear := (-625443155487416407859527207124195343750000000)
      constant := (7584860841714022703114230312675312421864790317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34976936318602678407/10000000000000000000)
  centralHi := (349769363186026784071/100000000000000000000)
  directionLo := (353320412228771303253/100000000000000000000)
  directionHi := (176660206114385651627/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree051.table
  base := (4033534530095881623072973226650960398021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-565499955312519446517134632471272250000000000)
      constant := (6981458383203443302802122551324761507478729589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree051.table
  base := (4027396175326237562011787819786233215517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-567076452827329177925974933911819125000000000)
      constant := (7020168747064156352098054169503028589223236953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353320412228771303253/100000000000000000000)
  centralHi := (176660206114385651627/50000000000000000000)
  directionLo := (178418062406430044731/50000000000000000000)
  directionHi := (356836124812860089463/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree052.table
  base := (4763165880517132770298648100046913053761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-5189364223915516404510208387258869000000000000)
      constant := (65371353691977093894848997359970427831805535241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree052.table
  base := (2378755578982051777479360648440856728399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-2601915453496296969895665576709590750000000000)
      constant := (32866804927445894358407162273711899930805055719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178418062406430044731/50000000000000000000)
  centralHi := (356836124812860089463/100000000000000000000)
  directionLo := (180158767650515167581/50000000000000000000)
  directionHi := (360317535301030335163/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree053.table
  base := (5505076359270585158963054138818673047643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-5289228850018357790366205082276287750000000000)
      constant := (67958741651348115034825768170319354704691206883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree053.table
  base := (5499869090680691933663834293543492990169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-5303973738539225278248887901631990875000000000)
      constant := (68335126119621587640510118760946067802361438589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180158767650515167581/50000000000000000000)
  centralHi := (360317535301030335163/100000000000000000000)
  directionLo := (363765628556848976339/100000000000000000000)
  directionHi := (18188281427842448817/5000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree054.table
  base := (48897661693416677524083736512034994691/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (94090)
      previous := (47045)
      next := (47045)
      square := (1439249495873354792070675197487500000000000)
      linear := (-74848520501683321891975024684634812500000000)
      constant := (980489699938182615971359290416355434912636904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree054.table
  base := (3127053591245008198924233532526531406731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5756997983493419168282700789950000000000000)
      linear := (-300228698338103145372580258324711125000000000)
      constant := (3943668710903517757448665165569530725802806979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363765628556848976339/100000000000000000000)
  centralHi := (18188281427842448817/5000000000000000000)
  directionLo := (73436268639769435713/20000000000000000000)
  directionHi := (183590671599423589283/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree055.table
  base := (7024308824925049061152270657358078823263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-5488958102224040562078198472311125250000000000)
      constant := (73280875974087454280093423354943672656426484103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree055.table
  base := (3509948851244885963417706074022298058639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-2752129700816243977582000699028804812500000000)
      constant := (36843157066118223303027960300067487033915327909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73436268639769435713/20000000000000000000)
  centralHi := (183590671599423589283/50000000000000000000)
  directionLo := (74113114916932151549/20000000000000000000)
  directionHi := (185282787292330378873/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree056.table
  base := (7801002484871203886233269869366549628401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-5588822728326881947934195167328544000000000000)
      constant := (76015569130100908166150197347253949039082625081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree056.table
  base := (7796944591684618526343131478632125736677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-5604402233179119293621558146270419000000000000)
      constant := (76435933056969184170394206695808403227007545037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74113114916932151549/20000000000000000000)
  centralHi := (185282787292330378873/50000000000000000000)
  directionLo := (2991353420416490501/800000000000000000)
  directionHi := (186959588776030656313/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree057.table
  base := (8588712161372106379414712906274160972607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-632076372714413703754465762482884750000000000)
      constant := (8755479448974539164056665360176297045435009263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree057.table
  base := (4292490201119099411392234078391949549769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5756997983493419168282700789950000000000000)
      linear := (-316919170262541701782173049693512687500000000)
      constant := (4401937273483961208241005401878902872356745271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2991353420416490501/800000000000000000)
  centralHi := (186959588776030656313/50000000000000000000)
  directionLo := (47155371117581897757/12500000000000000000)
  directionHi := (377242968940655182057/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree058.table
  base := (938719431283198724793590473325162989391/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84681000000000000000000000000000000000000000
      center := (677448)
      previous := (338724)
      next := (338724)
      square := (10362596370288154502908861421910000000000000)
      linear := (-578855198053256471964618855736338150000000000)
      constant := (8163209308275141587169252762169746725542119271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree058.table
  base := (7331065259774842328964391653772047899/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 21170250000000000000000000000000000000000000
      center := (169362)
      previous := (84681)
      next := (84681)
      square := (2590649092572038625727215355477500000000000)
      linear := (-145117197406809549263416791067400943750000000)
      constant := (2052077681759860783646848981396614367466420758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47155371117581897757/12500000000000000000)
  centralHi := (377242968940655182057/100000000000000000000)
  directionLo := (380537729915326934979/100000000000000000000)
  directionHi := (19026886495766346749/5000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree059.table
  base := (509811443409131060509089895556172909233/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42340500000000000000000000000000000000000000
      center := (338724)
      previous := (169362)
      next := (169362)
      square := (5181298185144077251454430710955000000000000)
      linear := (-294420830331770305275109262619040012500000000)
      constant := (4225694231010223498331268582769475510743947173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree059.table
  base := (10193075729305370337997617945997648349461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-5904830727819013308994228390908847125000000000)
      constant := (84980623618119339845386451759847212288591644441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380537729915326934979/100000000000000000000)
  centralHi := (19026886495766346749/5000000000000000000)
  directionLo := (191902104055075752199/50000000000000000000)
  directionHi := (383804208110151504399/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree060.table
  base := (688476060312969987129743856808491836069/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (94090)
      previous := (47045)
      next := (47045)
      square := (1439249495873354792070675197487500000000000)
      linear := (-83170572676920104046641415936086375000000000)
      constant := (1214509344628635056958397375431595910308646442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree060.table
  base := (2753179957869741630182434071998677963569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (188180)
      previous := (94090)
      next := (94090)
      square := (2878498991746709584141350394975000000000000)
      linear := (-166804821093490129095882920531157125000000000)
      constant := (2442427868613431534579001065420087182052970721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191902104055075752199/50000000000000000000)
  centralHi := (383804208110151504399/100000000000000000000)
  directionLo := (387043119609444373273/100000000000000000000)
  directionHi := (193521559804722186637/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree061.table
  base := (1184517890564392889765746700544851545097/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84681000000000000000000000000000000000000000
      center := (677448)
      previous := (338724)
      next := (338724)
      square := (10362596370288154502908861421910000000000000)
      linear := (-608814585884108887721417864241563775000000000)
      constant := (9042444244494539859472210755241789932674734057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree061.table
  base := (11842517731627978945271512339052467229371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-6105116390912275985909341887334465875000000000)
      constant := (90923431143973887952489877366589364859286303151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387043119609444373273/100000000000000000000)
  centralHi := (193521559804722186637/50000000000000000000)
  directionLo := (39025515078082036927/10000000000000000000)
  directionHi := (390255150780820369271/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree062.table
  base := (3171188077564034100373693266755298050153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25906490925720386257272153554775000000000000)
      linear := (-1547002621235982565767543834358264125000000000)
      constant := (23363294941192156377448065918993276359028756193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree062.table
  base := (12682308534739837294765202426321477585493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-6205259222458907324366898635547275250000000000)
      constant := (93968693615039838501322138202285328039510882733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39025515078082036927/10000000000000000000)
  centralHi := (390255150780820369271/100000000000000000000)
  directionLo := (98360239993388277049/25000000000000000000)
  directionHi := (393440959973553108197/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree063.table
  base := (422943451496811758201161069827154194073/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (94090)
      previous := (47045)
      next := (47045)
      square := (1439249495873354792070675197487500000000000)
      linear := (-87331598764538495123974611561812156250000000)
      constant := (1340706560380668785548819970597987247416100178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree063.table
  base := (2706389378959236563581127063325309651101/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2302799193397367667313080315980000000000000)
      linear := (-140120045644567525840543452972446325000000000)
      constant := (2156959519449671250087145503489211542999396809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98360239993388277049/25000000000000000000)
  centralHi := (393440959973553108197/100000000000000000000)
  directionLo := (3172809432753110779/800000000000000000)
  directionHi := (24787573693383677961/6250000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree064.table
  base := (14393360728411710018033233332926239443743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-6387739737149613034782168727467894000000000000)
      constant := (99657508964996832293151585103119042882335600983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree064.table
  base := (14391301512124140492648105253019976843079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-6405544885552170001282012131972894000000000000)
      constant := (100206874305972392480546338002572850659048772799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3172809432753110779/800000000000000000)
  centralHi := (24787573693383677961/6250000000000000000)
  directionLo := (4996705188371811201/1250000000000000000)
  directionHi := (399736415069744896081/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree065.table
  base := (3052428667932694909064504192284423359013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20725192740576309005817722843820000000000000)
      linear := (-1297520872650490884127633084497062550000000000)
      constant := (20566615894344671409517297626640272828683329853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree065.table
  base := (15260253775962132315174951201578305516369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-6505687717098801339739568880185703375000000000)
      constant := (103399771363173495994255225884946649379080080789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4996705188371811201/1250000000000000000)
  centralHi := (399736415069744896081/100000000000000000000)
  directionLo := (40284725120914198957/10000000000000000000)
  directionHi := (402847251209141989571/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree066.table
  base := (16140430016109194568039668008717228740091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-731940998817255089610462457500303500000000000)
      constant := (11784174966617020998261146771690354139590516219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree066.table
  base := (16138696538206903502223377137855875531703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-733981172071714742021902847599834750000000000)
      constant := (11849095608158887230749637163776648085221543527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40284725120914198957/10000000000000000000)
  centralHi := (402847251209141989571/100000000000000000000)
  directionLo := (405934248469763548607/100000000000000000000)
  directionHi := (6342722632340055447/1562500000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree067.table
  base := (681124917041384839888270264541921782757/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20725192740576309005817722843820000000000000)
      linear := (-1337466723091627438470031762504030050000000000)
      constant := (21866197272799786755267868895348971035396977585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree067.table
  base := (3405306601132917482163868192336645520839/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20725192740576309005817722843820000000000000)
      linear := (-1341194676038412803330936475322264425000000000)
      constant := (21986626688039481981365435782123590168217354859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405934248469763548607/100000000000000000000)
  centralHi := (6342722632340055447/1562500000000000000)
  directionLo := (408997946638686570839/100000000000000000000)
  directionHi := (10224948665967164271/2500000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree068.table
  base := (17925133666032843582953545128529413206363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-6787198241560978578206155507537569000000000000)
      constant := (112653306978971690856684296794854145927228025203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree068.table
  base := (17923675739353733763063801329969822200231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-6806116211738695355112239124824131500000000000)
      constant := (113273582859055382293513790474856753623112761311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408997946638686570839/100000000000000000000)
  centralHi := (10224948665967164271/2500000000000000000)
  directionLo := (103009716358643835141/25000000000000000000)
  directionHi := (82407773086915068113/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree069.table
  base := (3766276470476954725996983463660832284969/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2302799193397367667313080315980000000000000)
      linear := (-153045841503640443645825604501221950000000000)
      constant := (2578322883996405423901753159146995082688023321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree069.table
  base := (9415022875257466512319675906023759674559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5756997983493419168282700789950000000000000)
      linear := (-383681057960295927420544215168718937500000000)
      constant := (6481289002286487037668390937375046241789644381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103009716358643835141/25000000000000000000)
  centralHi := (82407773086915068113/20000000000000000000)
  directionLo := (51882188192119801537/12500000000000000000)
  directionHi := (415057505536958412297/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree070.table
  base := (19746796800004026803944620603399476183069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-6986927493766661349918148897572406500000000000)
      constant := (119444648653893293321205508752344416277033465989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree070.table
  base := (9872785841990714190363875839931502409529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-3503200937415979016013676310624875125000000000)
      constant := (60050992472037343463271647330603952162963200249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51882188192119801537/12500000000000000000)
  centralHi := (415057505536958412297/100000000000000000000)
  directionLo := (209027174774305625933/50000000000000000000)
  directionHi := (418054349548611251867/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree071.table
  base := (2583913972563449111676464046165658204633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12953245462860193128636076777387500000000000)
      linear := (-885849014983687841971768199073728156250000000)
      constant := (15364207259691517113231351215688177891000745823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree071.table
  base := (4134037816093650190060930645691934713893/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20725192740576309005817722843820000000000000)
      linear := (-1421308941275717874096981873892511925000000000)
      constant := (24717985221866486517847308210444907854561860633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209027174774305625933/50000000000000000000)
  centralHi := (418054349548611251867/100000000000000000000)
  directionLo := (105257465724070678189/25000000000000000000)
  directionHi := (421029862896282712757/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree072.table
  base := (10802434175893453993026657250779909364029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5756997983493419168282700789950000000000000)
      linear := (-399258708109574673423896793755958000000000000)
      constant := (7023975169971004418269696368304554792206148861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree072.table
  base := (5400959927538320048879525992581209149103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (188180)
      previous := (94090)
      next := (94090)
      square := (2878498991746709584141350394975000000000000)
      linear := (-200185764942367241915068503268760250000000000)
      constant := (3531306127943623241023470412700157643758910127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105257465724070678189/25000000000000000000)
  centralHi := (421029862896282712757/100000000000000000000)
  directionLo := (414047358080591371/97656250000000000)
  directionHi := (84796898934905112781/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree073.table
  base := (22547413252188802743480076178385633184561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-7286521372075185507486138982624662750000000000)
      constant := (129998329089481069157472534847340245862295560041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree073.table
  base := (11273235485330327096856281776074038045067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-3653415184735926023700011432944089187500000000)
      constant := (65356631989783454412948041131746316271456037377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414047358080591371/97656250000000000)
  centralHi := (84796898934905112781/20000000000000000000)
  directionLo := (426918678436962949877/100000000000000000000)
  directionHi := (213459339218481474939/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree074.table
  base := (23498898353079840767543318961282997200647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-7386385998178026893342135677642081500000000000)
      constant := (133613982091960297764073182140227914220322988607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree074.table
  base := (23498035343222752769147018055275069558313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-7406973201018483385857579614100987750000000000)
      constant := (134348652206185088192288058471439844692611253153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426918678436962949877/100000000000000000000)
  centralHi := (213459339218481474939/50000000000000000000)
  directionLo := (107458208234734548741/25000000000000000000)
  directionHi := (85966566587787638993/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree075.table
  base := (12229640082083804040066917094641954787649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5756997983493419168282700789950000000000000)
      linear := (-415902812460048237733229576258861125000000000)
      constant := (7626583799117461857809789478306975556893864441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree075.table
  base := (6114622475349608340387896063206364538481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (94090)
      previous := (47045)
      next := (47045)
      square := (1439249495873354792070675197487500000000000)
      linear := (-104265500452293260059932449476580515625000000)
      constant := (1917127522927375171984370131937664666067963552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107458208234734548741/25000000000000000000)
  centralHi := (85966566587787638993/20000000000000000000)
  directionLo := (432727362835149736543/100000000000000000000)
  directionHi := (13522730088598429267/3125000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree076.table
  base := (1589282461655920965804740573875888533971/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12953245462860193128636076777387500000000000)
      linear := (-948264406297963708131766133459614875000000000)
      constant := (17623988079758513400419191431110802444827896502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree076.table
  base := (12713897933634266365325708961867056726401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-3803629432055873031386346555263303250000000000)
      constant := (70883424514785854367653070632112325097835863081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432727362835149736543/100000000000000000000)
  centralHi := (13522730088598429267/3125000000000000000)
  directionLo := (217801329667780900787/50000000000000000000)
  directionHi := (17424106373422472063/4000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree077.table
  base := (13203290254255701194360546352668654011677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-3842989938243275525455062881347168875000000000)
      constant := (72377083923334064351447300000966285272784695037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree077.table
  base := (26405918210520474085732825930341108140741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-7707401695658377401230249858739415875000000000)
      constant := (145549651376185277934368107516988047104052026121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217801329667780900787/50000000000000000000)
  centralHi := (17424106373422472063/4000000000000000000)
  directionLo := (109614775205650220343/25000000000000000000)
  directionHi := (438459100822600881373/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree078.table
  base := (27393431441074820613219022129596706939101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-865093833621043604085124717523528500000000000)
      constant := (16507255032508186387258963318693563649965001309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree078.table
  base := (27392825286277213112574344405381140715697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-867504947467223193298645178550247250000000000)
      constant := (16597954001210209665609773386228683742837743073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109614775205650220343/25000000000000000000)
  centralHi := (438459100822600881373/100000000000000000000)
  directionLo := (441297053432394745027/100000000000000000000)
  directionHi := (110324263358098686257/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree079.table
  base := (28389043187624276342159077939689293658213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-7885709128692233822622119152729175250000000000)
      constant := (152425284520326995746701006657516479197364885053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree079.table
  base := (28388488507926301424822775906450176185097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-7907687358751640078145363355165034625000000000)
      constant := (153262650512948607161860925028814753852928636557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441297053432394745027/100000000000000000000)
  centralHi := (110324263358098686257/25000000000000000000)
  directionLo := (27757304475161356301/6250000000000000000)
  directionHi := (444116871602581700817/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree080.table
  base := (29393389546141836205967418008491205053421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-7985573754795075208478115847746594000000000000)
      constant := (156334133311115002871336727844588813735128743701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree080.table
  base := (3674110256445835376140394799364659911793/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12953245462860193128636076777387500000000000)
      linear := (-1000978773787283927075365012922230500000000000)
      constant := (19649105336945209140527511204358067672240543033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27757304475161356301/6250000000000000000)
  centralHi := (444116871602581700817/100000000000000000000)
  directionLo := (27932431161813153913/6250000000000000000)
  directionHi := (446918898589010462609/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree081.table
  base := (3800805854979438391003722012196112597233/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (94090)
      previous := (47045)
      next := (47045)
      square := (1439249495873354792070675197487500000000000)
      linear := (-112297755290248841587973785316166843750000000)
      constant := (2226275550832823279076625843751698414345334047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree081.table
  base := (30405982589017708922676863505305962883967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-900885891316100306117830761287850375000000000)
      constant := (17908017842586379927160035960621177983486183003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27932431161813153913/6250000000000000000)
  centralHi := (446918898589010462609/100000000000000000000)
  directionLo := (44970346695346300809/10000000000000000000)
  directionHi := (449703466953463008091/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree082.table
  base := (6285638734755368640990676970243644850241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20725192740576309005817722843820000000000000)
      linear := (-1637060601400151596038021847556286300000000000)
      constant := (32859680351025575937139360488333702361438258121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree082.table
  base := (31427769046630137011234951081572254831433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-8208115853391534093518033599803462750000000000)
      constant := (165200602391558154347657672559638975669974327873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44970346695346300809/10000000000000000000)
  centralHi := (449703466953463008091/100000000000000000000)
  directionLo := (226235449512181099693/50000000000000000000)
  directionHi := (452470899024362199387/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree083.table
  base := (8114652678747936672834391343293351147761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25906490925720386257272153554775000000000000)
      linear := (-2071291908275899841511526483199712562500000000)
      constant := (42088454489868308519174419507403202478504486741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree083.table
  base := (32458222387405629363518157653676256093359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-8308258684938165431975590348016272125000000000)
      constant := (169278166508331821881207097067103214142827670979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226235449512181099693/50000000000000000000)
  centralHi := (452470899024362199387/100000000000000000000)
  directionLo := (455221507332270880747/100000000000000000000)
  directionHi := (113805376833067720187/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree084.table
  base := (16748840246872128569583096501604557442609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5756997983493419168282700789950000000000000)
      linear := (-465835125511468930661227923767570500000000000)
      constant := (9581004821869146022212290781200146624727508081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree084.table
  base := (16748662707086114113108444059994595815973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5756997983493419168282700789950000000000000)
      linear := (-467133417582488709468508172012726750000000000)
      constant := (9633602859851372410587810408065682831719989957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455221507332270880747/100000000000000000000)
  centralHi := (113805376833067720187/25000000000000000000)
  directionLo := (457955595021848083293/100000000000000000000)
  directionHi := (228977797510924041647/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree085.table
  base := (8636346805992734991865048589528867737713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25906490925720386257272153554775000000000000)
      linear := (-2121224221327320534439524830708421937500000000)
      constant := (44152801730215606237828895406118600899483212053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree085.table
  base := (34545062591780972303927070737188431437749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-8508544348031428108890703844441890875000000000)
      constant := (177580655983004849684322031194579902522540960569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457955595021848083293/100000000000000000000)
  centralHi := (228977797510924041647/50000000000000000000)
  directionLo := (460673456241799443547/100000000000000000000)
  directionHi := (115168364060449860887/25000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree086.table
  base := (8900429160255077970733278306571711328507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25906490925720386257272153554775000000000000)
      linear := (-2146190377853030880903524004462776625000000000)
      constant := (45203294283295417868605482579943281708103051267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree086.table
  base := (8900354971621365038872837627042219123059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25906490925720386257272153554775000000000000)
      linear := (-2152171794894514861837065148163675062500000000)
      constant := (45451394709245145435498195659196547976895696679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460673456241799443547/100000000000000000000)
  centralHi := (115168364060449860887/25000000000000000000)
  directionLo := (463375376514241728023/100000000000000000000)
  directionHi := (57921922064280216003/12500000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree087.table
  base := (18333327927514799271290365266171691772709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5756997983493419168282700789950000000000000)
      linear := (-482479229861942494970560706270473625000000000)
      constant := (10281333129948661020833352215109809305311293981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree087.table
  base := (916659615521095217354367756360574776153/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704500000000000000000000000000000000000000
      center := (37636)
      previous := (18818)
      next := (18818)
      square := (575699798349341916828270078995000000000000)
      linear := (-48382388950692726587810096338152831250000000)
      constant := (1033775660920630241455139076011710902729444029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463375376514241728023/100000000000000000000)
  centralHi := (57921922064280216003/12500000000000000000)
  directionLo := (116515408271198583927/25000000000000000000)
  directionHi := (466061633084794335709/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree088.table
  base := (235876207615198985024806457094102190537/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21170250000000000000000000000000000000000000
      center := (169362)
      previous := (84681)
      next := (84681)
      square := (2590649092572038625727215355477500000000000)
      linear := (-219612269090445157383152235197148600000000000)
      constant := (4734091588805437192873278890356808376637454788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree088.table
  base := (9434986335660732267207347391549003669451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25906490925720386257272153554775000000000000)
      linear := (-2202243210667830531065843522270079750000000000)
      constant := (47600693849854644566778685207821692851607780131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116515408271198583927/25000000000000000000)
  centralHi := (466061633084794335709/100000000000000000000)
  directionLo := (234366247627306415361/50000000000000000000)
  directionHi := (468732495254612830723/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree089.table
  base := (1941115910311578482437477471855589709557/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42340500000000000000000000000000000000000000
      center := (338724)
      previous := (169362)
      next := (169362)
      square := (5181298185144077251454430710955000000000000)
      linear := (-444217769486032384059104305145168137500000000)
      constant := (9685608894066964949760460531166414338874683817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree089.table
  base := (970552292662250210990819813641717858259/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42340500000000000000000000000000000000000000
      center := (338724)
      previous := (169362)
      next := (169362)
      square := (5181298185144077251454430710955000000000000)
      linear := (-445455783710897673136046541864656418750000000)
      constant := (9738752363101888868673644342054969408924132633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234366247627306415361/50000000000000000000)
  centralHi := (468732495254612830723/100000000000000000000)
  directionLo := (235694112347745026143/50000000000000000000)
  directionHi := (471388224695490052287/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree090.table
  base := (19956510653909296503438964862126134905511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5756997983493419168282700789950000000000000)
      linear := (-499123334212416059279893488773376750000000000)
      constant := (11006085473392963873789637740055077108013452999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree090.table
  base := (39912814366847043036461459687477496285947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-1001028722862731644575387509500659750000000000)
      constant := (22132937084686837453749071893019124258648225323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235694112347745026143/50000000000000000000)
  centralHi := (471388224695490052287/100000000000000000000)
  directionLo := (237014537874534183247/50000000000000000000)
  directionHi := (94805815149813673299/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree091.table
  base := (20506146964603922513817688878789098397627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51812981851440772514544307109550000000000000)
      linear := (-4542042320963165226447039746469100125000000000)
      constant := (101277872371836195411809221661477691592581326987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree091.table
  base := (820242097628051384865938796403411475409/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84681000000000000000000000000000000000000000
      center := (677448)
      previous := (338724)
      next := (338724)
      square := (10362596370288154502908861421910000000000000)
      linear := (-910940133731121613963604433371874712500000000)
      constant := (20366693418494648034745296295585525309866641395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237014537874534183247/50000000000000000000)
  centralHi := (94805815149813673299/20000000000000000000)
  directionLo := (11916382392778286391/2500000000000000000)
  directionHi := (476655295711131455641/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree092.table
  base := (10530032076175157658140424999161246390819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25906490925720386257272153554775000000000000)
      linear := (-2295987317007292959687519046988904750000000000)
      constant := (51762698972882322770871253745005471052495943739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree092.table
  base := (42119955623781608298357147881425721860493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-9209544168857847478093601081931556500000000000)
      constant := (208186547884523547588080365851986284162243407733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11916382392778286391/2500000000000000000)
  centralHi := (476655295711131455641/100000000000000000000)
  directionLo := (479267125101875051167/100000000000000000000)
  directionHi := (14977097659433595349/3125000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree093.table
  base := (8647303483411850076768794768676871250079/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2302799193397367667313080315980000000000000)
      linear := (-206306975425155849435690508510511950000000000)
      constant := (4702104252675940997371550182081419355810743311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree093.table
  base := (43236359704691381357671880201417127834857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-1034409666711608757394573092238262875000000000)
      constant := (23639474919724504111148623878733410207946607013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479267125101875051167/100000000000000000000)
  centralHi := (14977097659433595349/3125000000000000000)
  directionLo := (240932398961496318151/50000000000000000000)
  directionHi := (481864797922992636303/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree094.table
  base := (2218072746268729000646904467000397716077/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42340500000000000000000000000000000000000000
      center := (338724)
      previous := (169362)
      next := (169362)
      square := (5181298185144077251454430710955000000000000)
      linear := (-469183926011742730523103478899522825000000000)
      constant := (10809371532169101333306904459427293396963866437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree094.table
  base := (11090327725171890798129553075341616854663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25906490925720386257272153554775000000000000)
      linear := (-2352457457987777538752178644589293812500000000)
      constant := (54343278209232489919882806039477762237143155003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240932398961496318151/50000000000000000000)
  centralHi := (481864797922992636303/100000000000000000000)
  directionLo := (30278033868897116413/6250000000000000000)
  directionHi := (484448541902353862609/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree095.table
  base := (45494935099885220674140929727346355383447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-9483543146337695996318066273007875250000000000)
      constant := (220829013225221411421087022334384648966319425407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree095.table
  base := (11373700897456156570354567481216980667797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12953245462860193128636076777387500000000000)
      linear := (-1188746582937217686683283915821248078125000000)
      constant := (27755007885834980801201865716251331790545913566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30278033868897116413/6250000000000000000)
  centralHi := (484448541902353862609/100000000000000000000)
  directionLo := (97403715745399956267/20000000000000000000)
  directionHi := (60877322340874972667/12500000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree096.table
  base := (46636952763078286747454544076303723333327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-1064823085826726375797118107558366000000000000)
      constant := (25057715408610947831042167905394827732843273743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree096.table
  base := (46636832693524996988879901670082880565623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11513995966986838336565401579900000000000000)
      linear := (-1067790610560485870213758674975866000000000000)
      constant := (25195124955190129964173512083560045823241946807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97403715745399956267/20000000000000000000)
  centralHi := (60877322340874972667/12500000000000000000)
  directionLo := (24478756213256478571/5000000000000000000)
  directionHi := (489575124265129571421/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree097.table
  base := (47787503236466460132273043140148071648423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (720)
      previous := (360)
      next := (360)
      square := (11013493857251731855573239900000000000000)
      linear := (-1029150005159249523650766251784750000000000)
      constant := (24472176278460452679024141600993703738585807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree097.table
  base := (47787393624066037660000436586543155066429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (720)
      previous := (360)
      next := (360)
      square := (11013493857251731855573239900000000000000)
      linear := (-1032018102517908828821488449675375000000000)
      constant := (24606365923959080540346100557470903044035361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell044.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24478756213256478571/5000000000000000000)
  centralHi := (489575124265129571421/100000000000000000000)
  directionLo := (492118388777707878291/100000000000000000000)
  directionHi := (123029597194426969573/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree098.table
  base := (9789316458498856039990263612402985763721/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20725192740576309005817722843820000000000000)
      linear := (-1956627404929244030777211271612026300000000000)
      constant := (47009363329367078758453727479373087059332658001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree098.table
  base := (48946482237141947463694673281629509601289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103625963702881545029088614219100000000000000)
      linear := (-9810401158137635508838941571208412750000000000)
      constant := (236335579881195344269102353970492207748640503809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell044.Kernel098
