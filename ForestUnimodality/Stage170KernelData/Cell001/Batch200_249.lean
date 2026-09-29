import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell001.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch200_249
import ForestUnimodality.BinomialMassData.Q9_35.Batch200_249

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel200
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96973565247465633293/25000000000000000000)
  centralHi := (387894260989862533173/100000000000000000000)
  directionLo := (194436279141901090253/50000000000000000000)
  directionHi := (388872558283802180507/100000000000000000000)

def endpointA : IntegerEndpointWitness 200 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree200.table
  base := (-3458417933751304036388980306930332207481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-4976305200750255593525328730000000000000)
      constant := (119318628270749635074021031193069667792519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 200 interval.damping) (curvature.centralUpper 200 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree200.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 200 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree200.table
  base := (-6916835868183665620718516821832517897029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-2508970948114111871544290675700000000000000)
      constant := (61999956778558845738718941694651033115227895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 200 interval.damping) (curvature.centralUpper 200 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree200.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 200 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 200 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel201
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194436279141901090253/50000000000000000000)
  centralHi := (388872558283802180507/100000000000000000000)
  directionLo := (6091381259638094593/1562500000000000000)
  directionHi := (389848400616838053953/100000000000000000000)

def endpointA : IntegerEndpointWitness 201 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree201.table
  base := (-6877588030276249114796289910853557798511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-10003025687033715923277000030000000000000)
      constant := (241170958889792407494814690275396442201489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 201 interval.damping) (curvature.centralUpper 201 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree201.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 201 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree201.table
  base := (-1375517606174819164243093537049473443513/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-2521675600068479465073329003340000000000000)
      constant := (62656369912037452082876596977562395031696575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 201 interval.damping) (curvature.centralUpper 201 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree201.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 201 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 201 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel202
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6091381259638094593/1562500000000000000)
  centralHi := (389848400616838053953/100000000000000000000)
  directionLo := (390821806378334255877/100000000000000000000)
  directionHi := (195410903189167127939/50000000000000000000)

def endpointA : IntegerEndpointWitness 202 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree202.table
  base := (-3418847296862394049988785313358226509891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5026720486283460329751671300000000000000)
      constant := (121858955329396974041240476194141773490109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 202 interval.damping) (curvature.centralUpper 202 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree202.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 202 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree202.table
  base := (-683769459424957828909781770270424618941/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1267190126011423529301183665490000000000000)
      constant := (31658104063925386144216148233134729841797275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 202 interval.damping) (curvature.centralUpper 202 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree202.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 202 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 202 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel203
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390821806378334255877/100000000000000000000)
  centralHi := (195410903189167127939/50000000000000000000)
  directionLo := (391792793729213099901/100000000000000000000)
  directionHi := (195896396864606549951/50000000000000000000)

def endpointA : IntegerEndpointWitness 203 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree203.table
  base := (-1699288893907805268459599435208381182021/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5051928129050062697864842585000000000000)
      constant := (123139055915360447932762126872708237635958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 203 interval.damping) (curvature.centralUpper 203 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree203.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 203 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree203.table
  base := (-6797155576091871540478777616994069545871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (624)
      previous := (216)
      next := (0)
      square := (3529069987324331535843979900000000000000)
      linear := (-363869271996744950304486522660000000000000)
      constant := (9139924488806039359848329075541207565894515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 203 interval.damping) (curvature.centralUpper 203 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree203.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 203 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 203 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel204
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (391792793729213099901/100000000000000000000)
  centralHi := (195896396864606549951/50000000000000000000)
  directionLo := (392761380605908422889/100000000000000000000)
  directionHi := (39276138060590842289/10000000000000000000)

def endpointA : IntegerEndpointWitness 204 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree204.table
  base := (-6755970993565864063775564270288071109811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-10154271543633330131956027740000000000000)
      constant := (248851562388002934816547801329711928890189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 204 interval.damping) (curvature.centralUpper 204 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree204.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 204 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree204.table
  base := (-6755970993970204680954039301427758874747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-2559789555931582245660443986260000000000000)
      constant := (64646159789107500643523673656158199075686985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 204 interval.damping) (curvature.centralUpper 204 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree204.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 204 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 204 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel205
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392761380605908422889/100000000000000000000)
  centralHi := (39276138060590842289/10000000000000000000)
  directionLo := (78745516944846273657/20000000000000000000)
  directionHi := (196863792362115684143/50000000000000000000)

def endpointA : IntegerEndpointWitness 205 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree205.table
  base := (-1678535216222479406784293215474292347391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5102343414583267434091185155000000000000)
      constant := (125719131156639432189101746247176415305218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 205 interval.damping) (curvature.centralUpper 205 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree205.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 205 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree205.table
  base := (-6714140865244823652753434242850851526907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-2572494207885949839189482313900000000000000)
      constant := (65316273225993187406342098134101541375907785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 205 interval.damping) (curvature.centralUpper 205 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree205.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 205 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 205 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel206
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78745516944846273657/20000000000000000000)
  centralHi := (196863792362115684143/50000000000000000000)
  directionLo := (394691423583150997753/100000000000000000000)
  directionHi := (197345711791575498877/50000000000000000000)

def endpointA : IntegerEndpointWitness 206 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree206.table
  base := (-6671665206758952070559750610119270536843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-10255102114699739604408712880000000000000)
      constant := (254038211589393114243854800144880729463157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 206 interval.damping) (curvature.centralUpper 206 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree206.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 206 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree206.table
  base := (-1334333041414092074653912547836730698331/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-2585198859840317432718520641540000000000000)
      constant := (65989811728096426487632389889628004894544525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 206 interval.damping) (curvature.centralUpper 206 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree206.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 206 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 206 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel207
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (394691423583150997753/100000000000000000000)
  centralHi := (197345711791575498877/50000000000000000000)
  directionLo := (98913228617123003377/25000000000000000000)
  directionHi := (395652914468492013509/100000000000000000000)

def endpointA : IntegerEndpointWitness 207 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree207.table
  base := (-1325708807225263165120243136515452991203/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-10305517400232944340635055450000000000000)
      constant := (256651410199392335981943806113672735043985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 207 interval.damping) (curvature.centralUpper 207 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree207.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 207 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree207.table
  base := (-6628544036399726981158452562144665415229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-2597903511794685026247558969180000000000000)
      constant := (66666775291263827913423822118666556973268895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 207 interval.damping) (curvature.centralUpper 207 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree207.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 207 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 207 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel208
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98913228617123003377/25000000000000000000)
  centralHi := (395652914468492013509/100000000000000000000)
  directionLo := (79322414891310360349/20000000000000000000)
  directionHi := (198306037228275900873/50000000000000000000)

def endpointA : IntegerEndpointWitness 208 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree208.table
  base := (-6584777369746469337724322529465648077213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-10355932685766149076861398020000000000000)
      constant := (259277858126522069147007755950534351922787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 208 interval.damping) (curvature.centralUpper 208 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree208.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 208 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree208.table
  base := (-3292388684993218655360275451434990223791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1305304081874526309888298648410000000000000)
      constant := (33673581955695353647156392629694427395171205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 208 interval.damping) (curvature.centralUpper 208 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree208.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 208 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 208 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel209
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79322414891310360349/20000000000000000000)
  centralHi := (198306037228275900873/50000000000000000000)
  directionLo := (397568920417638938271/100000000000000000000)
  directionHi := (12424028763051216821/3125000000000000000)

def endpointA : IntegerEndpointWitness 209 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree209.table
  base := (-3270182612089123354200268641942920007891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5203173985649676906543870295000000000000)
      constant := (130958777677111739818787591761182079992109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 209 interval.damping) (curvature.centralUpper 209 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree209.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 209 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree209.table
  base := (-3270182612194428813278278643384131670513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1311656407851710106652817812230000000000000)
      constant := (34015488792210144697736053964034887740724315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 209 interval.damping) (curvature.centralUpper 209 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree209.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 209 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 209 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel210
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (397568920417638938271/100000000000000000000)
  centralHi := (12424028763051216821/3125000000000000000)
  directionLo := (79704693803907046121/20000000000000000000)
  directionHi := (199261734509767615303/50000000000000000000)

def endpointA : IntegerEndpointWitness 210 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree210.table
  base := (-3247653807894023611222362751823073586507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5228381628416279274657041580000000000000)
      constant := (132285250933065084084415611635676926413493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 210 interval.damping) (curvature.centralUpper 210 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree210.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 210 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree210.table
  base := (-1623826903993222141989394789918393976263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (156)
      previous := (54)
      next := (0)
      square := (882267496831082883960994975000000000000)
      linear := (-94143480987778135958381212575000000000000)
      constant := (2454222010940818877152695314302856210830795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 210 interval.damping) (curvature.centralUpper 210 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree210.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 210 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 210 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel211
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79704693803907046121/20000000000000000000)
  centralHi := (199261734509767615303/50000000000000000000)
  directionLo := (3195805893847066451/800000000000000000)
  directionHi := (49934467091360413297/12500000000000000000)

def endpointA : IntegerEndpointWitness 211 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree211.table
  base := (-3224802280376479396788000076964671603357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5253589271182881642770212865000000000000)
      constant := (133618348823032523413528381116160328396643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 211 interval.damping) (curvature.centralUpper 211 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree211.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 211 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree211.table
  base := (-6449604560915180175466982893865112028239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-2648722119612155400363712279740000000000000)
      constant := (69408880073195345528789743115411047553081445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 211 interval.damping) (curvature.centralUpper 211 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree211.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 211 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 211 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel212
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3195805893847066451/800000000000000000)
  centralHi := (49934467091360413297/12500000000000000000)
  directionLo := (200212869912250847859/50000000000000000000)
  directionHi := (400425739824501695719/100000000000000000000)

def endpointA : IntegerEndpointWitness 212 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree212.table
  base := (-160081401876595381742800785859934052307/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5278796913949484010883384150000000000000)
      constant := (134958071339018640882167065102801318953860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 212 interval.damping) (curvature.centralUpper 212 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree212.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 212 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree212.table
  base := (-6403256075206181799989518235349986804549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-2661426771566522993892750607380000000000000)
      constant := (70102968881059880210043267185091253232885495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 212 interval.damping) (curvature.centralUpper 212 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree212.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 212 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 212 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel213
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200212869912250847859/50000000000000000000)
  centralHi := (400425739824501695719/100000000000000000000)
  directionLo := (100343373595157323857/25000000000000000000)
  directionHi := (401373494380629295429/100000000000000000000)

def endpointA : IntegerEndpointWitness 213 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree213.table
  base := (-6356262174528189454903108383828078464889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-10608009113432172757993110870000000000000)
      constant := (272608836946239300176613038152421921535111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 213 interval.damping) (curvature.centralUpper 213 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree213.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 213 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree213.table
  base := (-254250486986125145092119511165915544439/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-2674131423520890587421788935020000000000000)
      constant := (70800482726063759983520479373740767290311125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 213 interval.damping) (curvature.centralUpper 213 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree213.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 213 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 213 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel214
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100343373595157323857/25000000000000000000)
  centralHi := (401373494380629295429/100000000000000000000)
  directionLo := (201159508145050522417/50000000000000000000)
  directionHi := (80463803258020208967/20000000000000000000)

def endpointA : IntegerEndpointWitness 214 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree214.table
  base := (-6308622874773323626256684756838058394503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-10658424398965377494219453440000000000000)
      constant := (275314780435043859786786032318161941605497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 214 interval.damping) (curvature.centralUpper 214 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree214.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 214 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree214.table
  base := (-3154311437441483243644945221826175242549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1343418037737629090475413631330000000000000)
      constant := (35750710802189191560450083723176587065575495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 214 interval.damping) (curvature.centralUpper 214 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree214.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 214 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 214 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel215
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201159508145050522417/50000000000000000000)
  centralHi := (80463803258020208967/20000000000000000000)
  directionLo := (80652464251491317509/20000000000000000000)
  directionHi := (201631160628728293773/50000000000000000000)

def endpointA : IntegerEndpointWitness 215 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree215.table
  base := (-3130169095624499625639437212776440107279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5354419842249291115222898005000000000000)
      constant := (139016986564500589563673499415348559892721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 215 interval.damping) (curvature.centralUpper 215 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree215.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 215 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree215.table
  base := (-3130169095672608278742764587689671118193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1349770363714812887239932795150000000000000)
      constant := (36102892756109308466843091090516030576042715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 215 interval.damping) (curvature.centralUpper 215 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree215.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 215 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 215 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel216
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80652464251491317509/20000000000000000000)
  centralHi := (201631160628728293773/50000000000000000000)
  directionLo := (404203424803983639443/100000000000000000000)
  directionHi := (101050856200995909861/25000000000000000000)

def endpointA : IntegerEndpointWitness 216 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree216.table
  base := (-1552852034807586885736084784444713582007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5379627485015893483336069290000000000000)
      constant := (140383207506418063492660637971110572835986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 216 interval.damping) (curvature.centralUpper 216 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree216.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 216 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree216.table
  base := (-48526626088396730578372759963961154553/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 306250000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (3087936238908790093863482412500000000000)
      linear := (-339030672422999171001112989742500000000000)
      constant := (9114196805730263783277972537377272274152240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 216 interval.damping) (curvature.centralUpper 216 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree216.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 216 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 216 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel217
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404203424803983639443/100000000000000000000)
  centralHi := (101050856200995909861/25000000000000000000)
  directionLo := (202571171135348865649/50000000000000000000)
  directionHi := (405142342270697731299/100000000000000000000)

def endpointA : IntegerEndpointWitness 217 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree217.table
  base := (-6161832733820602426295683762563794758803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-10809670255564991702898481150000000000000)
      constant := (283512106071445469435666258783686205241197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 217 interval.damping) (curvature.centralUpper 217 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree217.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 217 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree217.table
  base := (-770229091736836828727409204339423977759/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43750000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (441133748415541441980497487500000000000)
      linear := (-48659821988185017170320397242500000000000)
      constant := (1314728364313368213690262647000120160778435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 217 interval.damping) (curvature.centralUpper 217 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree217.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 217 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 217 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel218
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202571171135348865649/50000000000000000000)
  centralHi := (405142342270697731299/100000000000000000000)
  directionLo := (406079088821259944257/100000000000000000000)
  directionHi := (203039544410629972129/50000000000000000000)

def endpointA : IntegerEndpointWitness 218 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree218.table
  base := (-6111611989953797430811358310129864499039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-10860085541098196439124823720000000000000)
      constant := (286271046289895172948903497344870135500961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 218 interval.damping) (curvature.centralUpper 218 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree218.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 218 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree218.table
  base := (-6111611990018813269010933556925528539569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-2737654683292728555066980573220000000000000)
      constant := (74339427375679350980759098770625245507805595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 218 interval.damping) (curvature.centralUpper 218 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree218.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 218 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 218 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel219
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406079088821259944257/100000000000000000000)
  centralHi := (203039544410629972129/50000000000000000000)
  directionLo := (407013679444834208031/100000000000000000000)
  directionHi := (12719177482651069001/3125000000000000000)

def endpointA : IntegerEndpointWitness 219 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree219.table
  base := (-189398310074918998966100469099554477121/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5455250413315700587675583145000000000000)
      constant := (144521617826708881057304569697532128366064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 219 interval.damping) (curvature.centralUpper 219 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree219.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 219 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree219.table
  base := (-3030372961227229089577796537697717603241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1375179667623548074298009450430000000000000)
      constant := (37528745682308154862693735703348059187205955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 219 interval.damping) (curvature.centralUpper 219 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree219.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 219 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 219 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel220
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (407013679444834208031/100000000000000000000)
  centralHi := (12719177482651069001/3125000000000000000)
  directionLo := (50993266119860710609/12500000000000000000)
  directionHi := (407946128958885684873/100000000000000000000)

def endpointA : IntegerEndpointWitness 220 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree220.table
  base := (-6009234545754940392418515411710425630513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-10960916112164605911577508860000000000000)
      constant := (291828674147409730574971923388289574369487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 220 interval.damping) (curvature.centralUpper 220 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree220.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 220 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree220.table
  base := (-240369381832199997458159981926654894553/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-2763063987201463742125057228500000000000000)
      constant := (75778980364781670409370643037499238770862875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 220 interval.damping) (curvature.centralUpper 220 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree220.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 220 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 220 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel221
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50993266119860710609/12500000000000000000)
  centralHi := (407946128958885684873/100000000000000000000)
  directionLo := (16355058080476868689/4000000000000000000)
  directionHi := (204438226005960858613/50000000000000000000)

def endpointA : IntegerEndpointWitness 221 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree221.table
  base := (-2978538937234234612600410533881849778157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5505665698848905323901925715000000000000)
      constant := (147313680878714501906056143884243150221843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 221 interval.damping) (curvature.centralUpper 221 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree221.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 221 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree221.table
  base := (-5957077874512393856343789017828659283801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-2775768639155831335654095556140000000000000)
      constant := (76503894372637153980426392832599978475468755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 221 interval.damping) (curvature.centralUpper 221 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree221.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 221 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 221 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel222
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16355058080476868689/4000000000000000000)
  centralHi := (204438226005960858613/50000000000000000000)
  directionLo := (102451165771544193349/25000000000000000000)
  directionHi := (409804663086176773397/100000000000000000000)

def endpointA : IntegerEndpointWitness 222 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree222.table
  base := (-2952137961410561905784344066351126885337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5530873341615507692015097000000000000000)
      constant := (148719649234596226239861838191148873114663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 222 interval.damping) (curvature.centralUpper 222 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree222.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 222 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree222.table
  base := (-2952137961429832320029585967151878098157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1394236645555099464591566941890000000000000)
      constant := (38616116692341709693376169615883789865951535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 222 interval.damping) (curvature.centralUpper 222 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree222.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 222 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 222 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel223
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102451165771544193349/25000000000000000000)
  centralHi := (409804663086176773397/100000000000000000000)
  directionLo := (51341347062530347921/12500000000000000000)
  directionHi := (410730776500242783369/100000000000000000000)

def endpointA : IntegerEndpointWitness 223 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree223.table
  base := (-5850828704939525715532515263639860518627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-11112161968764220120256536570000000000000)
      constant := (300264484268573455013795690572610139481373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 223 interval.damping) (curvature.centralUpper 223 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree223.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 223 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree223.table
  base := (-585082870497334198832831141236938117691/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1400588971532283261356086105710000000000000)
      constant := (38981998698729733425835041135940750805828525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 223 interval.damping) (curvature.centralUpper 223 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree223.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 223 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 223 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel224
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51341347062530347921/12500000000000000000)
  centralHi := (410730776500242783369/100000000000000000000)
  directionLo := (205827403205823108117/50000000000000000000)
  directionHi := (82330961282329243247/20000000000000000000)

def endpointA : IntegerEndpointWitness 224 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree224.table
  base := (-5796736234796178052213634555933092113323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-11162577254297424856482879140000000000000)
      constant := (303102919141599508299206998244066907886677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 224 interval.damping) (curvature.centralUpper 224 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree224.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 224 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree224.table
  base := (-1159347246965169675095888357677200446969/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (624)
      previous := (216)
      next := (0)
      square := (3529069987324331535843979900000000000000)
      linear := (-401983227859847730891601505580000000000000)
      constant := (11242740915363150409852743505790489921780425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 224 interval.damping) (curvature.centralUpper 224 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree224.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 224 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 224 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel225
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205827403205823108117/50000000000000000000)
  centralHi := (82330961282329243247/20000000000000000000)
  directionLo := (6446511981552706427/1562500000000000000)
  directionHi := (412576766819373211329/100000000000000000000)

def endpointA : IntegerEndpointWitness 225 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree225.table
  base := (-5741998526211807948780659579718538974777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-11212992539830629592709221710000000000000)
      constant := (305954603074449885208788985826531461025223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 225 interval.damping) (curvature.centralUpper 225 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree225.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 225 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree225.table
  base := (-5741998526237840141048792647274683220781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-2826587246973301709770248866700000000000000)
      constant := (79437800411545116635463329789417702610908655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 225 interval.damping) (curvature.centralUpper 225 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree225.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 225 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 225 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel226
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6446511981552706427/1562500000000000000)
  centralHi := (412576766819373211329/100000000000000000000)
  directionLo := (103374167891586009283/25000000000000000000)
  directionHi := (413496671566344037133/100000000000000000000)

def endpointA : IntegerEndpointWitness 226 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree226.table
  base := (-5686615592857663278374148217113986077791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-11263407825363834328935564280000000000000)
      constant := (308819536053453337869401095437886013922209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 226 interval.damping) (curvature.centralUpper 226 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree226.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 226 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree226.table
  base := (-1421653898220125755309489934551941363511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 612500000000000000000000000000000000000000
      center := (1092)
      previous := (378)
      next := (0)
      square := (6175872477817580187726964825000000000000)
      linear := (-709822974731917325824821798585000000000000)
      constant := (20044959851529804411445766764996774365939805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 226 interval.damping) (curvature.centralUpper 226 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree226.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 226 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 226 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel227
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103374167891586009283/25000000000000000000)
  centralHi := (413496671566344037133/100000000000000000000)
  directionLo := (207207267170919057631/50000000000000000000)
  directionHi := (414414534341838115263/100000000000000000000)

def endpointA : IntegerEndpointWitness 227 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree227.table
  base := (-1126117489651552955275353904402782750783/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-11313823110897039065161906850000000000000)
      constant := (311697718065085845545660658024236086246085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 227 interval.damping) (curvature.centralUpper 227 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree227.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 227 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree227.table
  base := (-5630587448277803209273760321626847034151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-2851996550882036896828325521980000000000000)
      constant := (80925303387950984182587846123433422476633005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 227 interval.damping) (curvature.centralUpper 227 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree227.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 227 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 227 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel228
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207207267170919057631/50000000000000000000)
  centralHi := (414414534341838115263/100000000000000000000)
  directionLo := (83066073736774162253/20000000000000000000)
  directionHi := (207665184341935405633/50000000000000000000)

def endpointA : IntegerEndpointWitness 228 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree228.table
  base := (-696739263223889326745282517096452943331/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5682119198215121900694124710000000000000)
      constant := (157294574547984203033196968471614188226676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 228 interval.damping) (curvature.centralUpper 228 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree228.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 228 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree228.table
  base := (-696739263226086875220820348014846906369/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306250000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (3087936238908790093863482412500000000000)
      linear := (-358087650354550561294670481202500000000000)
      constant := (10209274044220321555401015840630362507939595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 228 interval.damping) (curvature.centralUpper 228 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree228.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 228 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 228 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel229
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83066073736774162253/20000000000000000000)
  centralHi := (207665184341935405633/50000000000000000000)
  directionLo := (416244187981523159631/100000000000000000000)
  directionHi := (26015261748845197477/6250000000000000000)

def endpointA : IntegerEndpointWitness 229 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree229.table
  base := (-22066382314775449883594637127333543677/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5707326840981724268807295995000000000000)
      constant := (158746914566432434875916446487208307040375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 229 interval.damping) (curvature.centralUpper 229 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree229.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 229 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree229.table
  base := (-43098402958666297323226033977364508523/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 306250000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (3087936238908790093863482412500000000000)
      linear := (-359675731848846510485800272157500000000000)
      constant := (10303313287538892006409131298134731126589840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 229 interval.damping) (curvature.centralUpper 229 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree229.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 229 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 229 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel230
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (416244187981523159631/100000000000000000000)
  centralHi := (26015261748845197477/6250000000000000000)
  directionLo := (417156005477225657133/100000000000000000000)
  directionHi := (208578002738612828567/50000000000000000000)

def endpointA : IntegerEndpointWitness 230 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree230.table
  base := (-1091726376012286023631041463833338265299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-11465068967496653273840934560000000000000)
      constant := (320411758162679814831008285755833308673505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 230 interval.damping) (curvature.centralUpper 230 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree230.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 230 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree230.table
  base := (-1364657970018740316136749075047080612061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 612500000000000000000000000000000000000000
      center := (1092)
      previous := (378)
      next := (0)
      square := (6175872477817580187726964825000000000000)
      linear := (-722527626686284919353860126225000000000000)
      constant := (20795561306097076427277838979763465250045055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 230 interval.damping) (curvature.centralUpper 230 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree230.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 230 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 230 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel231
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417156005477225657133/100000000000000000000)
  centralHi := (208578002738612828567/50000000000000000000)
  directionLo := (104516458567249306621/25000000000000000000)
  directionHi := (83613166853799445297/20000000000000000000)

def endpointA : IntegerEndpointWitness 231 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree231.table
  base := (-1350005755712648872671291233550066546297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5757742126514929005033638565000000000000)
      constant := (161671468086228231684483427301024866907406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 231 interval.damping) (curvature.centralUpper 231 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree231.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 231 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree231.table
  base := (-5400023022862466186661334619405938411539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (624)
      previous := (216)
      next := (0)
      square := (3529069987324331535843979900000000000000)
      linear := (-414687879814215324420639833220000000000000)
      constant := (11991629874688525536242394461624792155596135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 231 interval.damping) (curvature.centralUpper 231 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree231.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 231 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 231 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel232
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104516458567249306621/25000000000000000000)
  centralHi := (83613166853799445297/20000000000000000000)
  directionLo := (104743421828160105293/25000000000000000000)
  directionHi := (418973687312640421173/100000000000000000000)

def endpointA : IntegerEndpointWitness 232 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree232.table
  base := (-5340769019881537201880723259658718794263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-11565899538563062746293619700000000000000)
      constant := (326287363149374636752316408380341281205737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 232 interval.damping) (curvature.centralUpper 232 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree232.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 232 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree232.table
  base := (-5340769019891951025372509076149631202093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-2915519810653874864473517160180000000000000)
      constant := (84703997992464318385623408688535340355487215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 232 interval.damping) (curvature.centralUpper 232 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree232.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 232 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 232 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel233
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104743421828160105293/25000000000000000000)
  centralHi := (418973687312640421173/100000000000000000000)
  directionLo := (104969894355973478061/25000000000000000000)
  directionHi := (83975915484778782449/20000000000000000000)

def endpointA : IntegerEndpointWitness 233 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree233.table
  base := (-1056173976767968084690910295879457683149/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-11616314824096267482519962270000000000000)
      constant := (329245039080748749809344277906852711584255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 233 interval.damping) (curvature.centralUpper 233 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree233.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 233 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree233.table
  base := (-5280869883848976016656590895371021083969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-2928224462608242458002555487820000000000000)
      constant := (85470011830214262347077160840426099834427595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 233 interval.damping) (curvature.centralUpper 233 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree233.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 233 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 233 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel234
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104969894355973478061/25000000000000000000)
  centralHi := (83975915484778782449/20000000000000000000)
  directionLo := (52597939660067908583/12500000000000000000)
  directionHi := (84156703456108653733/20000000000000000000)

def endpointA : IntegerEndpointWitness 234 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree234.table
  base := (-5097974245389126003793030001225866663/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5833365054814736109373152420000000000000)
      constant := (166107981977012921333786525026872356268544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 234 interval.damping) (curvature.centralUpper 234 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree234.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 234 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree234.table
  base := (-2610162813643239574228283150967546366617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1470464557281305025765796907730000000000000)
      constant := (43119725316497020415505993030976951140178835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 234 interval.damping) (curvature.centralUpper 234 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree234.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 234 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 234 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel235
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52597939660067908583/12500000000000000000)
  centralHi := (84156703456108653733/20000000000000000000)
  directionLo := (105421379856122753679/25000000000000000000)
  directionHi := (421685519424491014717/100000000000000000000)

def endpointA : IntegerEndpointWitness 235 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree235.table
  base := (-2579568131309838432451793868797244555027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5858572697581338477486323705000000000000)
      constant := (167600068878391824738634197034327755444973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 235 interval.damping) (curvature.centralUpper 235 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree235.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 235 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree235.table
  base := (-1289784065656676766057431609079008752979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 612500000000000000000000000000000000000000
      center := (1092)
      previous := (378)
      next := (0)
      square := (6175872477817580187726964825000000000000)
      linear := (-738408441629244411265158035775000000000000)
      constant := (21753078599440050852445212005925642855520145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 235 interval.damping) (curvature.centralUpper 235 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree235.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 235 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 235 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel236
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105421379856122753679/25000000000000000000)
  centralHi := (421685519424491014717/100000000000000000000)
  directionLo := (211292798131893460289/50000000000000000000)
  directionHi := (422585596263786920579/100000000000000000000)

def endpointA : IntegerEndpointWitness 236 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree236.table
  base := (-509730180215694301894628481552389420097/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5883780340347940845599494990000000000000)
      constant := (169098780238364351576998575832238052899515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 236 interval.damping) (curvature.centralUpper 236 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree236.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 236 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree236.table
  base := (-1019460360432621998595151469675991355049/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-2966338418471345238589670470740000000000000)
      constant := (87788603121500854777278823643454910590064975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 236 interval.damping) (curvature.centralUpper 236 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree236.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 236 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 236 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel237
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211292798131893460289/50000000000000000000)
  centralHi := (422585596263786920579/100000000000000000000)
  directionLo := (423483760074619455831/100000000000000000000)
  directionHi := (52935470009327431979/12500000000000000000)

def endpointA : IntegerEndpointWitness 237 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree237.table
  base := (-2517411129028395935322515095158635455281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5908987983114543213712666275000000000000)
      constant := (170604116050847237658563223302966364544719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 237 interval.damping) (curvature.centralUpper 237 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree237.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 237 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree237.table
  base := (-2517411129031100761651589124425715006661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1489521535212856416059354399190000000000000)
      constant := (44284158400617599552148412857291699823368055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 237 interval.damping) (curvature.centralUpper 237 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree237.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 237 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 237 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel238
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423483760074619455831/100000000000000000000)
  centralHi := (52935470009327431979/12500000000000000000)
  directionLo := (10609500575081732751/2500000000000000000)
  directionHi := (424380023003269310041/100000000000000000000)

def endpointA : IntegerEndpointWitness 238 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree238.table
  base := (-2485848821180319381341140634976288153809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5934195625881145581825837560000000000000)
      constant := (172116076309819775311986910742523711846191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 238 interval.damping) (curvature.centralUpper 238 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree238.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 238 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree238.table
  base := (-7954716227784614427117604402543747473/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (624)
      previous := (216)
      next := (0)
      square := (3529069987324331535843979900000000000000)
      linear := (-427392531768582917949678160860000000000000)
      constant := (12764493633430441830315629771670355524028125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 238 interval.damping) (curvature.centralUpper 238 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree238.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 238 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 238 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel239
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10609500575081732751/2500000000000000000)
  centralHi := (424380023003269310041/100000000000000000000)
  directionLo := (425274397068025859809/100000000000000000000)
  directionHi := (42527439706802585981/10000000000000000000)

def endpointA : IntegerEndpointWitness 239 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree239.table
  base := (-2453963983493289024093045112022600110891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-5959403268647747949939008845000000000000)
      constant := (173634661009322917360705612066102399889109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 239 interval.damping) (curvature.centralUpper 239 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree239.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 239 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree239.table
  base := (-2453963983495370217831737422778993036911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1502226187167224009588392726830000000000000)
      constant := (45069009508457302787693697213743146705956805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 239 interval.damping) (curvature.centralUpper 239 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree239.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 239 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 239 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel240
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425274397068025859809/100000000000000000000)
  centralHi := (42527439706802585981/10000000000000000000)
  directionLo := (85233378832213487537/20000000000000000000)
  directionHi := (213083447080533718843/50000000000000000000)

def endpointA : IntegerEndpointWitness 240 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree240.table
  base := (-4843513243731142278627389461122673358527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-11969221822828700636104360260000000000000)
      constant := (350319740286916795057967722138877326641473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 240 interval.damping) (curvature.centralUpper 240 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree240.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 240 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree240.table
  base := (-1210878310933698333666314145271914785967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 612500000000000000000000000000000000000000
      center := (1092)
      previous := (378)
      next := (0)
      square := (6175872477817580187726964825000000000000)
      linear := (-754289256572203903176455945325000000000000)
      constant := (22732001886762397341950644772408380877438085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 240 interval.damping) (curvature.centralUpper 240 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree240.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 240 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 240 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel241
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85233378832213487537/20000000000000000000)
  centralHi := (213083447080533718843/50000000000000000000)
  directionLo := (85411505210061247017/20000000000000000000)
  directionHi := (213528763025153117543/50000000000000000000)

def endpointA : IntegerEndpointWitness 241 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree241.table
  base := (-1194613371067757316896737930201189848483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6009818554180952686165351415000000000000)
      constant := (176691703706387866910031271382722620303034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 241 interval.damping) (curvature.centralUpper 241 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree241.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 241 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree241.table
  base := (-4778453484274231755715863881411538928293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3029861678243183206234862108940000000000000)
      constant := (91721421021557255374223268486942172962568215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 241 interval.damping) (curvature.centralUpper 241 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree241.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 241 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 241 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel242
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85411505210061247017/20000000000000000000)
  centralHi := (213528763025153117543/50000000000000000000)
  directionLo := (427946304381198648859/100000000000000000000)
  directionHi := (21397315219059932443/5000000000000000000)

def endpointA : IntegerEndpointWitness 242 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree242.table
  base := (-2356374350082398873482104546525648776151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6035026196947555054278522700000000000000)
      constant := (178230161692332046137898126960974351223849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 242 interval.damping) (curvature.centralUpper 242 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree242.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 242 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree242.table
  base := (-4712748700167606733503328437423407292061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3042566330197550799763900436580000000000000)
      constant := (92518259437605758591150894855143265213445055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 242 interval.damping) (curvature.centralUpper 242 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree242.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 242 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 242 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel243
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427946304381198648859/100000000000000000000)
  centralHi := (21397315219059932443/5000000000000000000)
  directionLo := (428833240678521859347/100000000000000000000)
  directionHi := (107208310169630464837/25000000000000000000)

def endpointA : IntegerEndpointWitness 243 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree243.table
  base := (-929279780570906462591084698605353885613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-12120467679428314844783387970000000000000)
      constant := (359550488191139785828972593693223230571935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 243 interval.damping) (curvature.centralUpper 243 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree243.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 243 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree243.table
  base := (-2323199451428498055052902127064124414311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1527635491075959196646469382110000000000000)
      constant := (46659261396195894973638155231505289518493805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 243 interval.damping) (curvature.centralUpper 243 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree243.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 243 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 243 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel244
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428833240678521859347/100000000000000000000)
  centralHi := (107208310169630464837/25000000000000000000)
  directionLo := (214859173174058703287/50000000000000000000)
  directionHi := (17188733853924696263/4000000000000000000)

def endpointA : IntegerEndpointWitness 244 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree244.table
  base := (-915880820733495668132556389393763314483/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-12170882964961519581009730540000000000000)
      constant := (362653901820875569104489375053031183427585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 244 interval.damping) (curvature.centralUpper 244 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree244.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 244 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree244.table
  base := (-1144851025917409833541083176166470212241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 612500000000000000000000000000000000000000
      center := (1092)
      previous := (378)
      next := (0)
      square := (6175872477817580187726964825000000000000)
      linear := (-766993908526571496705494272965000000000000)
      constant := (23530552770785043944420615043531214798000955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 244 interval.damping) (curvature.centralUpper 244 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree244.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 244 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 244 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel245
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214859173174058703287/50000000000000000000)
  centralHi := (17188733853924696263/4000000000000000000)
  directionLo := (53825204084825313853/12500000000000000000)
  directionHi := (17224065307144100433/4000000000000000000)

def endpointA : IntegerEndpointWitness 245 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree245.table
  base := (-4511764313817647528164925105081415947891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-12221298250494724317236073110000000000000)
      constant := (365770564262657430404267957351168584052109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 245 interval.damping) (curvature.centralUpper 245 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree245.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 245 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree245.table
  base := (-2255882156909771451815769745431241151113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (312)
      previous := (108)
      next := (0)
      square := (1764534993662165767921989950000000000000)
      linear := (-220048591861475255739358244250000000000000)
      constant := (6780666021935963177883639335109906559711045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 245 interval.damping) (curvature.centralUpper 245 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree245.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 245 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 245 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel246
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53825204084825313853/12500000000000000000)
  centralHi := (17224065307144100433/4000000000000000000)
  directionLo := (215741555421524931947/50000000000000000000)
  directionHi := (86296622168609972779/20000000000000000000)

def endpointA : IntegerEndpointWitness 246 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree246.table
  base := (-2221739772203697356802839579754875414113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6135856768013964526731207840000000000000)
      constant := (184450237752691507445082257197745124585887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 246 interval.damping) (curvature.centralUpper 246 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree246.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 246 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree246.table
  base := (-4443479544409057093929226830504815914749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3093384938015021173880053747140000000000000)
      constant := (95739862461561640267863440471894320100886495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 246 interval.damping) (curvature.centralUpper 246 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree246.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 246 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 246 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel247
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215741555421524931947/50000000000000000000)
  centralHi := (86296622168609972779/20000000000000000000)
  directionLo := (86472558380127319629/20000000000000000000)
  directionHi := (216181395950318299073/50000000000000000000)

def endpointA : IntegerEndpointWitness 247 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree247.table
  base := (-2187274903214483295989211420015079369593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6161064410780566894844379125000000000000)
      constant := (186021817769030037933592833728109920630407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 247 interval.damping) (curvature.centralUpper 247 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree247.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 247 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree247.table
  base := (-68352340725475384323105526504507455783/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 306250000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (3087936238908790093863482412500000000000)
      linear := (-388261198746173595926136509347500000000000)
      constant := (12069228192977692956339087070860165386665320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 247 interval.damping) (curvature.centralUpper 247 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree247.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 247 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 247 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel248
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86472558380127319629/20000000000000000000)
  centralHi := (216181395950318299073/50000000000000000000)
  directionLo := (216620343399131560881/50000000000000000000)
  directionHi := (433240686798263121763/100000000000000000000)

def endpointA : IntegerEndpointWitness 248 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree248.table
  base := (-1076243777691505735512511212649471018977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6186272053547169262957550410000000000000)
      constant := (187600022174902476778282263914701057962046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 248 interval.damping) (curvature.centralUpper 248 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree248.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 248 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree248.table
  base := (-4304975110767301678119274711143853064301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3118794241923756360938130402420000000000000)
      constant := (97371213551216698853690126093881755999246255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 248 interval.damping) (curvature.centralUpper 248 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree248.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 248 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 248 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel249
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216620343399131560881/50000000000000000000)
  centralHi := (433240686798263121763/100000000000000000000)
  directionLo := (217058403186071245273/50000000000000000000)
  directionHi := (434116806372142490547/100000000000000000000)

def endpointA : IntegerEndpointWitness 249 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree249.table
  base := (-2117377734097565479045103664638006183787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6211479696313771631070721695000000000000)
      constant := (189184850964920540382015716688486993816213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 249 interval.damping) (curvature.centralUpper 249 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree249.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 249 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree249.table
  base := (-2117377734098126225356412171773413059361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1565749446939061977233584365030000000000000)
      constant := (49096013240553423834621265304059513800456555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 249 interval.damping) (curvature.centralUpper 249 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree249.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 249 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 249 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell001.Kernel249
