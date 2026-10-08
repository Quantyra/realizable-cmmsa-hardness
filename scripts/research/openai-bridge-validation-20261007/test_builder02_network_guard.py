"""Regression coverage for the actual empty external-ip metadata response."""
import unittest
from unittest.mock import MagicMock
import urllib.error
from builder02_worker import require_no_external_ip

class NetworkGuard(unittest.TestCase):
    def opener(self,data,flavor='Google'):
        opener=MagicMock(); response=opener.open.return_value.__enter__.return_value
        response.headers={'Metadata-Flavor':flavor}; response.read.return_value=data
        return opener

    def test_empty_authenticated_external_ip_passes(self):
        opener=self.opener(b'')
        require_no_external_ip(opener)
        request=opener.open.call_args.args[0]
        self.assertTrue(request.full_url.endswith('/access-configs/0/external-ip'))

    def test_attached_external_ip_rejected(self):
        with self.assertRaisesRegex(RuntimeError,'External IP'): require_no_external_ip(self.opener(b'192.0.2.1'))

    def test_missing_metadata_header_rejected(self):
        with self.assertRaisesRegex(RuntimeError,'unauthenticated'): require_no_external_ip(self.opener(b'',flavor=''))

    def test_server_error_is_not_treated_as_no_ip(self):
        opener=MagicMock(); opener.open.side_effect=urllib.error.HTTPError('http://metadata',500,'failure',{},None)
        with self.assertRaises(urllib.error.HTTPError): require_no_external_ip(opener)

if __name__ == '__main__': unittest.main()
