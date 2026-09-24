plugins {
    alias(libs.plugins.kotlinMultiplatform)
    alias(libs.plugins.androidLibrary)
}

// Standalone build of the Kotlin minisat port. Compiles the port against ksat-common
// (mounted at common/). The byte-for-byte shadow tests, benchmarks and the Ksat facade
// live in the main repo (sat-solvers-kotlin), which consumes this repo as a submodule.
kotlin {
    androidTarget()
    jvm()

    js { browser(); nodejs() }

    @OptIn(org.jetbrains.kotlin.gradle.ExperimentalWasmDsl::class)
    wasmJs { browser(); nodejs() }

    iosArm64()
    iosSimulatorArm64()
    iosX64()

    sourceSets {
        val commonMain by getting {
            dependencies {
                implementation(project(":ksat-common"))
            }
        }
    }
}

android {
    namespace = "org.bytefred.ksat.minisat"
    compileSdk = libs.versions.android.compileSdk.get().toInt()
    defaultConfig {
        minSdk = libs.versions.android.minSdk.get().toInt()
    }
}
