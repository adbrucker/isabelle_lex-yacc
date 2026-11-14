/** A module declaration. */
@Deprecated(since = "1")
open module demo.app {
    requires transitive java.logging;
    requires static java.compiler;
    exports demo to demo.friend, demo.other;
    opens demo.internal;
    uses demo.Service;
    provides demo.Service with demo.Impl, demo.Other;
}
