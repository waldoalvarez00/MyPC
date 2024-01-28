#!/usr/bin/env python3

# Copyright Jamie Iles, 2017
# Copyright Waldo Alvarez, 2024
#
# This file is part of s80x86.
#
# s80x86 is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# s80x86 is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with s80x86.  If not, see <http://www.gnu.org/licenses/>.

import argparse
import os
import pystache
import struct
import paramiko

pystache.defaults.DELIMITERS = (u'<%', u'%>')

HERE = os.path.dirname(__file__)
MIF_TEMPLATE = os.path.join(HERE, 'bios.mif.templ')

import paramiko

def download_file(sftp_details, remote_path, local_path):
    try:
        with paramiko.Transport((sftp_details['host'], sftp_details['port'])) as transport:
            transport.connect(username=sftp_details['username'], password=sftp_details['password'])
            with paramiko.SFTPClient.from_transport(transport) as sftp:
                sftp.get(remote_path, local_path)
        return True
    except paramiko.ssh_exception.NoValidConnectionsError:
        print("Could not connect to the SFTP server. Check the host and port.")
    except paramiko.ssh_exception.AuthenticationException:
        print("Authentication failed. Check your username and password.")
    except paramiko.ssh_exception.SSHException as e:
        print(f"SSH error occurred: {e}")
    except FileNotFoundError:
        print(f"The file {remote_path} was not found on the SFTP server.")
    except Exception as e:
        print(f"An unexpected error occurred: {e}")

    return False


def write_mif(binary, output):
    with open(binary, 'rb') as b:
        data = bytearray(b.read())
    vals = []
    for i in range(len(data) // 2):
        vals.append(struct.unpack('<H', data[i*2:i*2 + 2])[0])

    data = {
        'depth': len(data) // 2,
        'width': '16',
        'values': [
            {'address': '{0:04x}'.format(a),
             'value': '{0:04x}'.format(v)} for a, v in enumerate(vals)
        ]
    }
    with open(MIF_TEMPLATE) as f:
        template = f.read()
    with open(output, 'w') as output:
        output.write(pystache.render(template, data))

parser = argparse.ArgumentParser()
parser.add_argument('--binary', help='Path to the local binary file')
parser.add_argument('--output', help='Output file path', required=True)
parser.add_argument('--sftp-host', help='SFTP host')
parser.add_argument('--sftp-port', type=int, default=22, help='SFTP port')
parser.add_argument('--sftp-username', help='SFTP username')
parser.add_argument('--sftp-password', help='SFTP password')
parser.add_argument('--sftp-remote-path', help='SFTP remote path to the binary file')
args = parser.parse_args()

# Determine whether to download from SFTP or use a local file

if args.sftp_host and args.sftp_remote_path:
    sftp_details = {
        'host': args.sftp_host,
        'port': args.sftp_port,
        'username': args.sftp_username,
        'password': args.sftp_password
    }
    local_binary_path = 'bios-mypc.bin'
    if download_file(sftp_details, args.sftp_remote_path, local_binary_path):
        binary_path = local_binary_path
    else:
        raise Exception("Failed to download the file from SFTP.")
elif args.binary:
    binary_path = args.binary
    if not os.path.exists(binary_path):
        raise Exception("The specified binary file does not exist.")
else:
    parser.error("Please specify either a local binary file or provide SFTP details.")

# Process the file
write_mif(binary_path, args.output)  # Use binary_path instead of args.binary
