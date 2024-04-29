organization := "ni-apr"

name := "microc"

version := "0.1"

scalaVersion := "2.13.6"

scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature")

libraryDependencies += "com.lihaoyi" %% "mainargs" % "0.4.0"
libraryDependencies += "org.scalameta" %% "munit" % "0.7.29" % Test


testFrameworks += new TestFramework("munit.Framework")

// --------------------------------------------------------------------
// ASSEMBLY
// --------------------------------------------------------------------
assembly / assemblyJarName := "microc.jar"
