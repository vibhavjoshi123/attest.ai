"""Connection settings, taken from the environment so nothing is hardcoded.

The defaults are a local TypeDB 3 server with the stock admin credentials,
which is what the quickstart assumes. A deployment points somewhere else by
setting the environment instead of editing code:

    TYPEDB_ADDRESS   host:port, or https://host:port for a TLS endpoint
    TYPEDB_USERNAME
    TYPEDB_PASSWORD
    TYPEDB_TLS       1 / true / yes to require TLS
                     (TYPEDB_TLS_ENABLED is accepted as well)
    TYPEDB_TLS_ROOT_CA   path to a CA bundle, when not using the system roots
"""

from __future__ import annotations

import os
from dataclasses import dataclass


def _flag(name: str, default: bool = False) -> bool:
    raw = os.environ.get(name)
    if raw is None:
        return default
    return raw.strip().lower() in {"1", "true", "yes", "on"}


@dataclass(frozen=True)
class StoreConfig:
    address: str = "127.0.0.1:1729"
    username: str = "admin"
    password: str = "password"
    tls: bool = False
    tls_root_ca: str | None = None

    @classmethod
    def from_env(cls) -> StoreConfig:
        address = os.environ.get("TYPEDB_ADDRESS", cls.address)
        return cls(
            address=address,
            username=os.environ.get("TYPEDB_USERNAME", cls.username),
            password=os.environ.get("TYPEDB_PASSWORD", cls.password),
            # an https:// endpoint implies TLS whether or not the flag is set.
            # TYPEDB_TLS_ENABLED is the name TypeDB's own tooling uses, and a
            # deployment that sets only that one must not silently connect
            # without TLS — it fails as a 404 from the TLS port, which reads
            # like a bad address rather than a missing flag.
            tls=_flag("TYPEDB_TLS",
                      _flag("TYPEDB_TLS_ENABLED",
                            address.startswith("https://"))),
            tls_root_ca=os.environ.get("TYPEDB_TLS_ROOT_CA") or None,
        )

    def candidates(self) -> list[str]:
        """Addresses to try, in order.

        Without TLS the bare ``host:port`` is the only valid form. With TLS
        the ``https://`` prefix is required — the driver refuses a bare
        address — and the advertised port is not always the one serving the
        driver protocol, so a managed endpoint gets the usual alternatives
        tried after the address as given.
        """
        address = self.address.strip().rstrip("/")
        if not self.tls:
            return [address.removeprefix("https://").removeprefix("http://")]

        bare = address.removeprefix("https://").removeprefix("http://")
        host, _, port = bare.rpartition(":")
        if not host:                       # no port given
            host, port = bare, "1729"
        seen, out = set(), []
        for candidate_port in (port, "443", "80", "1729"):
            url = f"https://{host}:{candidate_port}"
            if url not in seen:
                seen.add(url)
                out.append(url)
        return out
