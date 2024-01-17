organization := "ni-apr"

name := "microc"

version := "0.1"

scalaVersion := "2.13.6"

scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature")

libraryDependencies += "com.lihaoyi" %% "mainargs" % "0.4.0"
libraryDependencies += "org.scalameta" %% "munit" % "0.7.29" % Test
//libraryDependencies +="com.microsoft.z3" % "z3" % "4.8.13"


testFrameworks += new TestFramework("munit.Framework")

// --------------------------------------------------------------------
// ASSEMBLY
// --------------------------------------------------------------------
assembly / assemblyJarName := "microc.jar"

// --------------------------------------------------------------------
// DOCKER
// --------------------------------------------------------------------
enablePlugins(DockerPlugin)
docker / dockerfile := {
  val artifact: File = assembly.value
  val artifactTargetPath = "/" + artifact.name

  new Dockerfile {
    from("eclipse-temurin:17-alpine")
    add(artifact, artifactTargetPath)
    entryPoint("java", "-jar", artifactTargetPath)
  }
}

// create both latest and current version
val imageOrgName = s"fikovnik"
docker / imageNames := Seq(
  ImageName(s"$imageOrgName/${name.value}:latest"),
  ImageName(s"$imageOrgName/${name.value}:${version.value}")
)

// --------------------------------------------------------------------
// JMH
// --------------------------------------------------------------------
enablePlugins(JmhPlugin)

// --------------------------------------------------------------------
// BUILD INFO
// --------------------------------------------------------------------
/*enablePlugins(BuildInfoPlugin)
buildInfoKeys := Seq[BuildInfoKey](
  name,
  version,
  BuildInfoKey.action("gitCommit") {
    java.lang.Runtime
      .getRuntime()
      .exec("git rev-parse --short HEAD")
      .inputReader()
      .readLine()
      .strip()
  }
)*/
